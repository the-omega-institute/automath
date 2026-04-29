import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-depth prime-slice package.  The same finite prefix indexes the slice layer,
the exact external tower, and the prime-register ledger; the displayed map is the composite of
the two prefix-preserving injections. -/
structure conclusion_primeslice_finite_depth_ledger_incompatibility_Data where
  conclusion_primeslice_finite_depth_ledger_incompatibility_depth : ℕ

namespace conclusion_primeslice_finite_depth_ledger_incompatibility_Data

/-- The depth-`N` prime-slice layer. -/
abbrev conclusion_primeslice_finite_depth_ledger_incompatibility_slice
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :=
  Fin D.conclusion_primeslice_finite_depth_ledger_incompatibility_depth

/-- The exact finite-depth tower carrying the same prefix. -/
abbrev conclusion_primeslice_finite_depth_ledger_incompatibility_tower
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :=
  Fin D.conclusion_primeslice_finite_depth_ledger_incompatibility_depth

/-- The prime-register target ledger for the same finite prefix. -/
abbrev conclusion_primeslice_finite_depth_ledger_incompatibility_primeRegister
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :=
  Fin D.conclusion_primeslice_finite_depth_ledger_incompatibility_depth

/-- Prefix-preserving injection from the slice layer into the exact tower. -/
def conclusion_primeslice_finite_depth_ledger_incompatibility_sliceToTower
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :
    D.conclusion_primeslice_finite_depth_ledger_incompatibility_slice →
      D.conclusion_primeslice_finite_depth_ledger_incompatibility_tower :=
  fun i => i

/-- Prefix-preserving injection from the exact tower into the prime-register ledger. -/
def conclusion_primeslice_finite_depth_ledger_incompatibility_towerToRegister
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :
    D.conclusion_primeslice_finite_depth_ledger_incompatibility_tower →
      D.conclusion_primeslice_finite_depth_ledger_incompatibility_primeRegister :=
  fun i => i

/-- The exact prime-slice externalization map, expressed as the composite injection. -/
def conclusion_primeslice_finite_depth_ledger_incompatibility_e
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :
    D.conclusion_primeslice_finite_depth_ledger_incompatibility_slice →
      D.conclusion_primeslice_finite_depth_ledger_incompatibility_primeRegister :=
  D.conclusion_primeslice_finite_depth_ledger_incompatibility_towerToRegister ∘
    D.conclusion_primeslice_finite_depth_ledger_incompatibility_sliceToTower

/-- A finite-rank additive ledger would have to contain the depth prefix in rank `r` and also
compress it below that same prefix. -/
def conclusion_primeslice_finite_depth_ledger_incompatibility_finiteRankAdditiveLedgerExists
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) : Prop :=
  ∃ r : ℕ,
    D.conclusion_primeslice_finite_depth_ledger_incompatibility_depth ≤ r ∧
      r < D.conclusion_primeslice_finite_depth_ledger_incompatibility_depth

end conclusion_primeslice_finite_depth_ledger_incompatibility_Data

open conclusion_primeslice_finite_depth_ledger_incompatibility_Data

/-- Paper label: `thm:conclusion-primeslice-finite-depth-ledger-incompatibility`. -/
theorem paper_conclusion_primeslice_finite_depth_ledger_incompatibility
    (D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data) :
    Function.Injective
        D.conclusion_primeslice_finite_depth_ledger_incompatibility_e ∧
      ¬ D.conclusion_primeslice_finite_depth_ledger_incompatibility_finiteRankAdditiveLedgerExists := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simpa [conclusion_primeslice_finite_depth_ledger_incompatibility_e,
      conclusion_primeslice_finite_depth_ledger_incompatibility_sliceToTower,
      conclusion_primeslice_finite_depth_ledger_incompatibility_towerToRegister] using hxy
  · rintro ⟨r, hcontains, hcompresses⟩
    exact (Nat.not_lt_of_ge hcontains) hcompresses

end Omega.Conclusion
