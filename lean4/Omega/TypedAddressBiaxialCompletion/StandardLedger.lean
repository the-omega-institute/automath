import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.TypedAddressBiaxialCompletion.PhaseLedgerTemplate

namespace Omega.TypedAddressBiaxialCompletion

open Omega.CircleDimension

/-- Chapter-local ledger package for the standard biaxial prototype. The data records the visible
phase rank, the chapter-local ledger template carrying the standard extension witness, and the
register rank in the nontrivial and trivial denominator cases. -/
structure StandardLedgerData (Recorder : Type*) where
  rank : Nat
  modulus : Nat
  recorder : Recorder
  template : PhaseLedgerTemplate
  visibleCircleDim_eq_rank : circleDim rank 0 = rank
  registerCircleDim : Nat
  registerCircleDim_eq_rank_of_nontrivial : modulus ≠ 1 → registerCircleDim = rank
  registerCircleDim_eq_zero_of_trivial : modulus = 1 → registerCircleDim = 0

/-- Paper-facing refined ledger value `(cdim, pcdim; τ^rec)` for the standard biaxial prototype. -/
abbrev standardLedgerValue {Recorder : Type*} (D : StandardLedgerData Recorder) :
    Nat × Nat × Recorder :=
  (D.rank, D.registerCircleDim, D.recorder)

/-- The standard biaxial prototype has visible circle rank `r`; its register circle rank is `r`
when the denominator modulus is nontrivial and collapses to `0` when the modulus is `1`.
    prop:typed-address-biaxial-completion-standard-ledger -/
theorem paper_typed_address_biaxial_completion_standard_ledger
    {Recorder : Type*} (D : StandardLedgerData Recorder) :
    circleDim D.rank 0 = D.rank ∧
      standardLedgerValue D =
        if D.modulus ≠ 1 then
          (D.rank, D.rank, D.recorder)
        else
          (D.rank, 0, D.recorder) := by
  refine ⟨D.visibleCircleDim_eq_rank, ?_⟩
  by_cases h : D.modulus ≠ 1
  · simp [standardLedgerValue, D.registerCircleDim_eq_rank_of_nontrivial h, h]
  · have h1 : D.modulus = 1 := by omega
    simp [standardLedgerValue, D.registerCircleDim_eq_zero_of_trivial h1, h]

end Omega.TypedAddressBiaxialCompletion
