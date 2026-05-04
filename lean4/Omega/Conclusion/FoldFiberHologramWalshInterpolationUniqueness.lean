import Mathlib.Tactic
import Omega.Core.WalshFourier
import Omega.Folding.Fiber

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete finite-cube data for the fold-fiber hologram interpolation uniqueness statement. -/
structure conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_data where
  conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m : ℕ
  conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x :
    X conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m
  conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_y :
    X conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m

/-- Indicator of a fold fiber, used as the multilinear hologram coefficients on the cube. -/
def conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_fiberIndicator
    {m : ℕ} (x : X m) (w : Word m) : ℤ :=
  by
    classical
    exact if Fold w = x then 1 else 0

/-- Walsh coefficient of the fiber hologram. -/
def conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_walshCoefficient
    {m : ℕ} (x : X m) (I : Finset (Fin m)) : ℤ :=
  Omega.Core.walshBias
    (conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_fiberIndicator x) I

/-- Evaluation at a sign vertex is the corresponding Walsh coefficient. -/
def conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_signVertexEvaluation
    {m : ℕ} (x : X m) (I : Finset (Fin m)) : ℤ :=
  conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_walshCoefficient x I

namespace conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_data

/-- Equality of all sign-vertex hologram evaluations identifies the fold fiber. -/
def conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_statement
    (D : conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_data) : Prop :=
  (∀ I : Finset (Fin D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m),
    conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_signVertexEvaluation
        D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x I =
      conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_signVertexEvaluation
        D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_y I) →
    D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x =
      D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_y

end conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_data

/-- Paper label: `thm:conclusion-fold-fiber-hologram-walsh-interpolation-uniqueness`. -/
theorem paper_conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness
    (D : conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_data) :
    D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_statement := by
  classical
  intro hvertex
  let fX : Word D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m → ℤ :=
    conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_fiberIndicator
      D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x
  let fY : Word D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m → ℤ :=
    conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_fiberIndicator
      D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_y
  let w : Word D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m :=
    X.choosePreimage D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x
  have hcoeff :
      ∀ I : Finset (Fin D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m),
        Omega.Core.walshBias fX I = Omega.Core.walshBias fY I := by
    intro I
    simpa [conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_signVertexEvaluation,
      conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_walshCoefficient, fX, fY]
      using hvertex I
  have hsum :
      (∑ I : Finset (Fin D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m),
          Omega.Core.walshBias fX I * Omega.Core.walshChar I w) =
        ∑ I : Finset (Fin D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m),
          Omega.Core.walshBias fY I * Omega.Core.walshChar I w := by
    refine Finset.sum_congr rfl ?_
    intro I _hI
    rw [hcoeff I]
  have hinversion :
      ((2 : ℤ) ^ D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m) *
          fX w =
        ((2 : ℤ) ^ D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m) *
          fY w := by
    calc
      ((2 : ℤ) ^ D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m) *
          fX w =
          ∑ I : Finset (Fin D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m),
            Omega.Core.walshBias fX I * Omega.Core.walshChar I w := by
            exact Omega.Core.paper_walsh_fourier_inversion_completeness fX w
      _ =
          ∑ I : Finset (Fin D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m),
            Omega.Core.walshBias fY I * Omega.Core.walshChar I w := hsum
      _ =
          ((2 : ℤ) ^ D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m) *
            fY w := by
            exact (Omega.Core.paper_walsh_fourier_inversion_completeness fY w).symm
  have hfX : fX w = 1 := by
    have hFoldX :
        Fold w = D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x := by
      simp [w]
    simp [fX, conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_fiberIndicator,
      hFoldX]
  have hpow :
      (2 : ℤ) ^ D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_m ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hfY : fY w = 1 := by
    apply mul_left_cancel₀ hpow
    simpa [hfX] using hinversion.symm
  have hFold :
      Fold w = D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_y := by
    by_cases hy :
        Fold w = D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_y
    · exact hy
    · have hzero : fY w = 0 := by
        simp [fY, conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_fiberIndicator, hy]
      omega
  exact (X.Fold_choosePreimage
    D.conclusion_fold_fiber_hologram_walsh_interpolation_uniqueness_x).symm.trans hFold

end

end Omega.Conclusion
