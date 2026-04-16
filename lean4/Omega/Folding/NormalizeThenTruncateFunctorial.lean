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

set_option maxHeartbeats 400000 in
/-- Paper-facing corollary: multiscale invariants are exactly the fold-aware ones, while naive
truncate-then-fold picks up gauge artifacts precisely when the local defect is nonzero.
    cor:multiscale-auditable-invariants -/
theorem paper_multiscale_auditable_invariants (m : Nat) :
    let naiveRestrict : Omega.Word (m + 1) → Omega.X m := fun w => Omega.Fold (Omega.truncate w)
    let foldAwareRestrict : Omega.Word (m + 1) → Omega.X m := fun w => Omega.X.restrict (Omega.Fold w)
    (∀ w, naiveRestrict w = foldAwareRestrict w ↔ Omega.localDefect w = Omega.zeroWord m) ∧
      (∀ w, Omega.localDefect w ≠ Omega.zeroWord m → naiveRestrict w ≠ foldAwareRestrict w) ∧
      (∀ rhat : Omega.Word (m + 1) → Omega.X m,
        (∀ w, Omega.Fold (rhat w).1 = Omega.X.restrict (Omega.Fold w)) → rhat = foldAwareRestrict) := by
  let naiveRestrict : Omega.Word (m + 1) → Omega.X m := fun w => Omega.Fold (Omega.truncate w)
  let foldAwareRestrict : Omega.Word (m + 1) → Omega.X m := fun w => Omega.X.restrict (Omega.Fold w)
  rcases paper_normalize_then_truncate_functorial m with ⟨_, hcommute, hunique⟩
  refine ⟨?_, ?_, ?_⟩
  · intro w
    simpa [naiveRestrict, foldAwareRestrict] using hcommute w
  · intro w hdefect hEq
    have hiff :
        naiveRestrict w = foldAwareRestrict w ↔ Omega.localDefect w = Omega.zeroWord m := by
      simpa [naiveRestrict, foldAwareRestrict] using hcommute w
    exact hdefect (hiff.mp hEq)
  · intro rhat hnat
    exact hunique rhat hnat

end Omega.Folding
