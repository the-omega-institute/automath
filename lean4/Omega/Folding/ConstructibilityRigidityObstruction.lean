import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber
import Omega.Folding.MicrostateResidualWindowReachability
import Omega.Folding.Rewrite

namespace Omega.Folding

open scoped BigOperators

/-- The Dirac mass at a stable target `x`, used to specialize the residual-window theorem. -/
noncomputable def pointMass {m : ℕ} (x : X m) : X m → ℝ :=
  by
    classical
    exact fun y => if y = x then 1 else 0

lemma pointMass_nonneg {m : ℕ} (x : X m) : ∀ y, 0 ≤ pointMass x y := by
  classical
  intro y
  by_cases hy : y = x <;> simp [pointMass, hy]

lemma pointMass_sum {m : ℕ} (x : X m) : ∑ y, pointMass x y = 1 := by
  classical
  simp [pointMass]

lemma residualWindow_pointMass {m : ℕ} (x : X m) :
    residualWindow (pointMass x) X.fiberMultiplicity = Real.log (X.fiberMultiplicity x : ℝ) := by
  classical
  unfold residualWindow pointMass
  simp

/-- Paper-facing package for the constructibility/rigidity/obstruction trichotomy of `Fold_m`.
The constructibility layer is witnessed by surjectivity and idempotence, the rigidity layer is the
Newman-style uniqueness of irreducible representatives inside a value class, and the obstruction
layer is the `π = δ_x` specialization of the residual-window interval `[0, log d_m(x)]`.
    thm:fold-constructibility-rigidity-obstruction -/
theorem paper_fold_constructibility_rigidity_obstruction
    (m : ℕ) (x : X m) :
    Function.Surjective (Fold (m := m)) ∧
      Fold x.1 = x ∧
      (∀ a b : Rewrite.DigitCfg, Rewrite.Irreducible a → Rewrite.Irreducible b →
        Rewrite.value a = Rewrite.value b → a = b) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∃ fiberResidual : X m → ℝ,
          (∀ y, fiberResidual y = t * Real.log (X.fiberMultiplicity y : ℝ)) ∧
          (∑ y, pointMass x y * fiberResidual y =
            t * Real.log (X.fiberMultiplicity x : ℝ)) ∧
          (0 ≤ t * Real.log (X.fiberMultiplicity x : ℝ) ∧
            t * Real.log (X.fiberMultiplicity x : ℝ) ≤
              Real.log (X.fiberMultiplicity x : ℝ)) := by
  refine ⟨Fold_surjective m, Fold_stable x, ?_, ?_⟩
  · intro a b hIrrA hIrrB hVal
    exact Rewrite.irreducible_eq_of_value_eq hIrrA hIrrB hVal
  · intro t ht0 ht1
    obtain ⟨fiberResidual, hResidual, _hPointwiseBounds, hWeighted, hInterval, _hAffine,
        _hEntropy⟩ :=
      paper_fold_microstate_residual_window_reachability
        (pi := pointMass x) (d := X.fiberMultiplicity) (Hpi := 0)
        (pointMass_nonneg x) (by simpa using pointMass_sum x) X.fiberMultiplicity_pos t ht0 ht1
    refine ⟨fiberResidual, hResidual, ?_, ?_⟩
    · simpa [residualWindow_pointMass x] using hWeighted
    · simpa [residualWindow_pointMass x] using hInterval

end Omega.Folding
