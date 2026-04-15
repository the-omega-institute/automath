import Omega.Folding.Defect

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: the fold-aware restriction `ω ↦ π(Fold ω)` is the canonical
"normalize then truncate" map. It restores the Fold/restriction square, agrees with naive
truncate-then-fold exactly on zero-defect words, and is the unique map to `X m` satisfying the
same naturality square.
    thm:normalize-then-truncate-functorial -/
theorem paper_normalize_then_truncate_functorial (m : Nat) :
    let foldAwareRestrict : Omega.Word (m + 1) → Omega.X m :=
      fun ω => Omega.X.restrict (Omega.Fold ω)
    (∀ ω, Omega.Fold (foldAwareRestrict ω).1 = Omega.X.restrict (Omega.Fold ω)) ∧
      (∀ ω,
        Omega.Fold (Omega.truncate ω) = foldAwareRestrict ω ↔
          Omega.localDefect ω = Omega.zeroWord m) ∧
      (∀ rhat : Omega.Word (m + 1) → Omega.X m,
        (∀ ω, Omega.Fold (rhat ω).1 = Omega.X.restrict (Omega.Fold ω)) →
          rhat = foldAwareRestrict) := by
  let foldAwareRestrict : Omega.Word (m + 1) → Omega.X m :=
    fun ω => Omega.X.restrict (Omega.Fold ω)
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    simpa [foldAwareRestrict] using
      (Omega.Fold_stable (Omega.X.restrict (Omega.Fold ω)))
  · intro ω
    simpa [foldAwareRestrict] using (Omega.paper_fold_omega_commute (m := m) ω)
  · intro rhat hnat
    funext ω
    calc
      rhat ω = Omega.Fold (rhat ω).1 := (Omega.Fold_stable (rhat ω)).symm
      _ = Omega.X.restrict (Omega.Fold ω) := hnat ω
      _ = foldAwareRestrict ω := rfl

end Omega.Folding
