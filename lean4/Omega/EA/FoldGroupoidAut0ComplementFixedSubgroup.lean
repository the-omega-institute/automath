import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.ComplementPhaseLockingFixedpoints

namespace Omega.EA

open scoped BigOperators
open Omega

/-- The real dimension contributed by the factor indexed by `x`, using `dim_R PU(d) = d^2 - 1`. -/
noncomputable def foldGroupoidAut0FactorRealDim {m : ℕ} (x : X m) : ℝ :=
  (X.fiberMultiplicity x : ℝ) ^ 2 - 1

/-- The fixed-point locus of the complement involution on `X_m`. -/
noncomputable def foldGroupoidAut0ComplementFixedPoints (m : ℕ) : Finset (X m) :=
  Finset.filter (fun x : X m => Omega.complementAction (m := m) x = x) Finset.univ

/-- The moving locus of the complement involution on `X_m`. -/
noncomputable def foldGroupoidAut0ComplementMovingPoints (m : ℕ) : Finset (X m) :=
  Finset.filter (fun x : X m => Omega.complementAction (m := m) x ≠ x) Finset.univ

/-- The total real dimension of the connected fold-groupoid automorphism product. -/
noncomputable def foldGroupoidAut0RealDim (m : ℕ) : ℝ :=
  ∑ x : X m, foldGroupoidAut0FactorRealDim x

/-- The fixed-point contribution to the complement-fixed subgroup. -/
noncomputable def foldGroupoidAut0ComplementFixedContribution (m : ℕ) : ℝ :=
  (foldGroupoidAut0ComplementFixedPoints m).sum foldGroupoidAut0FactorRealDim

/-- Orbitwise dimension of the complement-fixed subgroup: fixed points contribute their whole
factor, and each moving pair contributes a single diagonal copy, hence half of the moving sum. -/
noncomputable def foldGroupoidAut0ComplementFixedSubgroupRealDim (m : ℕ) : ℝ :=
  foldGroupoidAut0ComplementFixedContribution m +
    (1 / 2 : ℝ) *
      (foldGroupoidAut0ComplementMovingPoints m).sum foldGroupoidAut0FactorRealDim

/-- Paper label: `prop:fold-groupoid-aut0-complement-fixed-subgroup`. The complement action is an
involution on `X_m`, and the corresponding fixed subgroup has the expected orbitwise real
dimension formula. -/
theorem paper_fold_groupoid_aut0_complement_fixed_subgroup (m : ℕ) (hm : 2 ≤ m) :
    Function.Involutive (Omega.complementAction (m := m)) ∧
      foldGroupoidAut0ComplementFixedSubgroupRealDim m =
        (foldGroupoidAut0RealDim m + foldGroupoidAut0ComplementFixedContribution m) / 2 := by
  refine ⟨Omega.complementAction_involutive m hm, ?_⟩
  classical
  have hsplit :
      foldGroupoidAut0RealDim m =
        foldGroupoidAut0ComplementFixedContribution m +
          (foldGroupoidAut0ComplementMovingPoints m).sum foldGroupoidAut0FactorRealDim := by
    unfold foldGroupoidAut0RealDim foldGroupoidAut0ComplementFixedContribution
      foldGroupoidAut0ComplementFixedPoints foldGroupoidAut0ComplementMovingPoints
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (X m)))
        (p := fun x : X m => Omega.complementAction (m := m) x = x)
        (f := fun x : X m => foldGroupoidAut0FactorRealDim x)).symm
  rw [hsplit]
  unfold foldGroupoidAut0ComplementFixedSubgroupRealDim
  ring

end Omega.EA
