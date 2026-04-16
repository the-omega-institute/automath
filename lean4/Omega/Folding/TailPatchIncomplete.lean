import Omega.Folding.Defect

namespace Omega.Folding

open Finset

set_option maxHeartbeats 400000 in
/-- Paper-facing corollary: once a raw tail patch is required to land in the stable sector and
commute with the fold-aware restriction square, it is forced to coincide with the canonical
fold-aware restriction. Any uniform bound on the resulting gauge anomaly therefore contradicts any
available witness whose anomaly exceeds that bound.
    cor:fold-tail-patch-incomplete -/
theorem paper_fold_tail_patch_incomplete
    (m R : Nat)
    (hwitness : ∃ ω : Omega.Word (m + 1),
      R < (Finset.univ.filter (fun i => Omega.localDefect ω i = true)).card) :
    ¬ ∃ T : Omega.Word (m + 1) → Omega.Word m,
        (∀ ω, Omega.Fold (T ω) = Omega.X.restrict (Omega.Fold ω)) ∧
        (∀ ω, (Omega.Fold (T ω)).1 = T ω) ∧
        (∀ ω,
          (Finset.univ.filter
            (fun i => Omega.xorWord (Omega.Fold (Omega.truncate ω)).1 (T ω) i = true)).card ≤ R) := by
  intro hpatch
  rcases hpatch with ⟨T, hcommute, hstable, htail⟩
  rcases hwitness with ⟨ω, hwitness⟩
  have hEq : T ω = (Omega.X.restrict (Omega.Fold ω)).1 := by
    calc
      T ω = (Omega.Fold (T ω)).1 := by symm; exact hstable ω
      _ = (Omega.X.restrict (Omega.Fold ω)).1 := by
        simpa using congrArg Subtype.val (hcommute ω)
  have hbound :
      (Finset.univ.filter (fun i => Omega.localDefect ω i = true)).card ≤ R := by
    simpa [Omega.localDefect, hEq] using htail ω
  exact Nat.not_le_of_lt hwitness hbound

end Omega.Folding
