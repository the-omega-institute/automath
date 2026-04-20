import Omega.Folding.Defect
import Omega.Folding.SummableNatEventuallyZero

namespace Omega.Folding.NaivePrefixLift

open Omega

/-- A compatible family in the restriction inverse system determines an inverse-limit point whose
finite prefixes recover the family. -/
theorem paper_fold_naive_prefix_lift_seeds
    (x : ∀ m : ℕ, X m)
    (h : ∀ m, X.restrict (x (m + 1)) = x m) :
    ∃ xInf : X.XInfinity, ∀ m, X.prefixWord xInf m = x m := by
  let F : X.CompatibleFamily := ⟨x, h⟩
  refine ⟨X.ofFamily F, ?_⟩
  intro m
  simpa [F, X.toFamily] using X.toFamily_ofFamily_seq F m

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_fold_naive_prefix_lift_package
    (x : ∀ m : ℕ, X m)
    (h : ∀ m, X.restrict (x (m + 1)) = x m) :
    ∃ xInf : X.XInfinity, ∀ m, X.prefixWord xInf m = x m :=
  paper_fold_naive_prefix_lift_seeds x h

/-- Paper label: `prop:fold-naive-prefix-lift`. -/
theorem paper_fold_naive_prefix_lift
    (x : ∀ m : ℕ, Omega.X m)
    (δMass : ℕ → ℕ) (C : ℕ)
    (hcompat : ∀ m, δMass m = 0 ↔ Omega.X.restrict (x (m + 1)) = x m)
    (hbd : ∀ n, ∑ i ∈ Finset.range n, δMass i ≤ C) :
    ∃ M : ℕ, ∃ xInf : Omega.X.XInfinity, ∀ m, M ≤ m → Omega.X.prefixWord xInf m = x m := by
  obtain ⟨M, hM⟩ :=
    Omega.Folding.SummableNatEventuallyZero.paper_fold_naive_prefix_lift_summable_core
      δMass C hbd
  let seq : ∀ m : ℕ, Omega.X m := fun m =>
    if hm : m ≤ M then Omega.X.restrictLE hm (x M) else x m
  have hseq : ∀ m, Omega.X.restrict (seq (m + 1)) = seq m := by
    intro m
    by_cases hm1 : m + 1 ≤ M
    · have hm : m ≤ M := Nat.le_trans (Nat.le_succ m) hm1
      calc
        Omega.X.restrict (seq (m + 1))
            = Omega.X.restrict (Omega.X.restrictLE hm1 (x M)) := by simp [seq, hm1]
        _ = Omega.X.restrictLE (Nat.le_succ m) (Omega.X.restrictLE hm1 (x M)) := by
            rw [Omega.X.restrictLE_succ]
        _ = Omega.X.restrictLE (Nat.le_trans (Nat.le_succ m) hm1) (x M) := by
            rw [Omega.X.restrictLE_comp]
        _ = Omega.X.restrictLE hm (x M) := by simp
        _ = seq m := by simp [seq, hm]
    · by_cases hm : m ≤ M
      · have hMle : M ≤ m := Nat.lt_succ_iff.mp (lt_of_not_ge hm1)
        have hm_eq : m = M := Nat.le_antisymm hm hMle
        subst m
        have htail : Omega.X.restrict (x (M + 1)) = x M := by
          exact (hcompat M).mp (hM M le_rfl)
        simpa [seq, hm1] using htail
      · have hMle : M ≤ m := Nat.le_of_lt (lt_of_not_ge hm)
        have htail : Omega.X.restrict (x (m + 1)) = x m := by
          exact (hcompat m).mp (hM m hMle)
        simpa [seq, hm, hm1] using htail
  obtain ⟨xInf, hxInf⟩ := paper_fold_naive_prefix_lift_package seq hseq
  refine ⟨M, xInf, ?_⟩
  intro m hm
  by_cases hm' : m ≤ M
  · have hm_eq : m = M := Nat.le_antisymm hm' hm
    subst m
    simpa [seq] using hxInf M
  · simpa [seq, hm'] using hxInf m

end Omega.Folding.NaivePrefixLift
