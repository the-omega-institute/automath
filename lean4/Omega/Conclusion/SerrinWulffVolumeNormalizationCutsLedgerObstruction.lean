import Omega.Conclusion.SerrinWulffScaleLedgerImpossibility
import Omega.Zeta.XiTerminalGbcStabilizedTerminalObject

namespace Omega.Conclusion

/-- After volume normalization, the Wulff scale family collapses to a singleton. -/
abbrev conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class :
    Type :=
  Unit

/-- The normalized class embeds trivially into every finite rational ledger. -/
def conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_embed
    (k : ℕ) :
    conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class ↪
      conclusion_serrin_wulff_scale_ledger_impossibility_rational_ledger k where
  toFun _ := 0
  inj' := by
    intro x y
    cases x
    cases y
    intro _
    rfl

/-- The quotient attached to the normalized singleton class has the expected terminal map. -/
def conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_terminal_factorization :
    Prop :=
  ∃! f :
      Omega.Zeta.xi_terminal_gbc_stabilized_terminal_object_bc_quotient
          (fun _ :
            conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class =>
              ())
          (fun _ :
            conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class =>
              ()) →
        conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class,
    ∀ x,
      f
          (Omega.Zeta.xi_terminal_gbc_stabilized_terminal_object_projection
            (fun _ :
              conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class =>
                ())
            (fun _ :
              conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class =>
                ()) x) =
        ()

/-- Paper-facing package for the fact that volume normalization kills the additive and
prime-register ledger obstructions by collapsing the scale family to the one-point case. -/
def conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_statement : Prop :=
  Fintype.card
      conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class = 1 ∧
    (∀ x :
      conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class,
      x = ()) ∧
    (∀ k : ℕ,
      Nonempty
        (conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class ↪
          conclusion_serrin_wulff_scale_ledger_impossibility_rational_ledger k)) ∧
    conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_terminal_factorization

/-- Paper label:
`cor:conclusion-serrin-wulff-volume-normalization-cuts-ledger-obstruction`. -/
theorem paper_conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction :
    conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_statement := by
  refine ⟨by simp [
    conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_normalized_class], ?_,
    ?_, ?_⟩
  · intro x
    cases x
    rfl
  · intro k
    exact ⟨conclusion_serrin_wulff_volume_normalization_cuts_ledger_obstruction_embed k⟩
  · refine ⟨fun _ => (), ?_, ?_⟩
    · intro x
      rfl
    · intro g hg
      funext q
      cases g q
      rfl

end Omega.Conclusion
