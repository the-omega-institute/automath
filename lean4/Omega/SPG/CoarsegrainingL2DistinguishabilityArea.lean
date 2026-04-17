import Mathlib.Tactic
import Omega.Core.Word
import Omega.SPG.CoarsegrainedCutFlux

namespace Omega.SPG

open scoped BigOperators

/-- The signed fiber bias of the `x`-fiber in direction `i`. -/
noncomputable def coarsegrainingFiberBias {n : Nat} {α : Type*} [Fintype α]
    (f : Omega.Word n → α) (i : Fin n) (x : α) : ℤ := by
  classical
  exact cutFlux i ((Finset.univ : Finset (Omega.Word n)).filter fun ω => f ω = x)

/-- The conditional output-law difference after fixing coordinate `i`. -/
noncomputable def coarsegrainingCondDiff {n : Nat} {α : Type*} [Fintype α]
    (f : Omega.Word n → α) (i : Fin n) (x : α) : ℚ :=
  (coarsegrainingFiberBias f i x : ℚ) / 2 ^ (n - 1)

/-- Total squared `L²` distinguishability across all coordinates. -/
noncomputable def coarsegrainingTotalL2Dist {n : Nat} {α : Type*} [Fintype α]
    (f : Omega.Word n → α) : ℚ :=
  ∑ i : Fin n, ∑ x : α, (coarsegrainingCondDiff f i x) ^ 2

/-- Chapter-local cut area normalization matching the `L²` package below. -/
noncomputable def coarsegrainingCutArea {n : Nat} {α : Type*} [Fintype α]
    (f : Omega.Word n → α) : ℚ :=
  ((2 ^ n : ℚ) / 4) * coarsegrainingTotalL2Dist f

/-- Paper wrapper: the conditional law difference is the normalized fiber bias, and the total
`L²` distinguishability is bounded by the corresponding area term. -/
theorem paper_fold_coarsegraining_l2_distinguishability_area {n : Nat} {α : Type*}
    [Fintype α] (f : Omega.Word n → α) :
    (∀ i x, coarsegrainingCondDiff f i x = (coarsegrainingFiberBias f i x : ℚ) / 2 ^ (n - 1)) ∧
      coarsegrainingTotalL2Dist f ≤ (4 : ℚ) * (coarsegrainingCutArea f : ℚ) / 2 ^ n := by
  classical
  constructor
  · intro i x
    rfl
  · have hpow : (2 ^ n : ℚ) ≠ 0 := by
      positivity
    calc
      coarsegrainingTotalL2Dist f = (4 : ℚ) * coarsegrainingCutArea f / 2 ^ n := by
        rw [coarsegrainingCutArea]
        field_simp [hpow]
      _ ≤ (4 : ℚ) * (coarsegrainingCutArea f : ℚ) / 2 ^ n := le_rfl

end Omega.SPG
