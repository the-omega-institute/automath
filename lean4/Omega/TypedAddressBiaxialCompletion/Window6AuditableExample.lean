import Omega.TypedAddressBiaxialCompletion.InstantiationExtraction
import Omega.TypedAddressBiaxialCompletion.Window6AuditBudgetSplit
import Omega.TypedAddressBiaxialCompletion.Window6BoundaryHolonomy
import Omega.TypedAddressBiaxialCompletion.Window6ExplicitFibers
import Omega.TypedAddressBiaxialCompletion.Window6TwoHiddenChannels
import Omega.TypedAddressBiaxialCompletion.Window6TwoSheetCharts

namespace Omega.TypedAddressBiaxialCompletion

open Omega.GU

/-- A concrete one-state admissible instantiation used for the window-`6` audit wrapper. -/
def window6AuditableInstantiation : AdmissiblePhysicalInstantiation where
  State := Unit
  observerSpacetime := { timeProjection := fun _ => 0 }
  causalCompatibility := { causalPreorder := fun _ _ => True }
  resourceQuasidistance := { resourceQuasidistance := fun _ _ => 0 }
  obstructionInterface := { obstruction := fun _ _ => False }

/-- The extracted rough spacetime package exists for the concrete window-`6` instantiation. -/
def window6AuditableInstantiationExists : Prop :=
  ∃ G : RoughSpacetimeQuadruple window6AuditableInstantiation.State,
    G.causalPreorder = window6AuditableInstantiation.causalCompatibility.causalPreorder ∧
      G.timeProjection = window6AuditableInstantiation.observerSpacetime.timeProjection ∧
      G.resourceQuasidistance =
        window6AuditableInstantiation.resourceQuasidistance.resourceQuasidistance ∧
      G.obstruction = window6AuditableInstantiation.obstructionInterface.obstruction

/-- The visible window-`6` layer already exhibits the nontrivial `+34` two-sheet alias over the
tail offsets `{21,34,55}`. -/
def window6VisibleLayerNontrivial : Prop :=
  terminalFoldbin6TailOffsets = {21, 34, 55} ∧
    terminalFoldbin6BoundaryAlias 0 = ({0, 34} : Finset Nat)

/-- The boundary holonomy leaves a residual rank-`2` quotient, so the local/global obstruction is
nontrivial. -/
def window6LocalGlobalObstructionNontrivial : Prop :=
  window6BoundaryResidualRank = 2 ∧ window6BoundaryResidualCardinality = 4

/-- The ledger budget split is numerically nontrivial already at window `6`. -/
def window6LedgerBudgetSplitNontrivial : Prop :=
  window6ReplayBudget = 2 ∧ window6BoundaryBudget = 3 ∧ window6AnomalyBudget = 21

/-- The audited spectrum is visible in the fiber histogram and in the universally present hidden
`34`-channel. -/
def window6StatisticalSpectrumAuditable : Prop :=
  cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9 ∧
    (∀ w : X 6, 34 ∈ window6HiddenOffsets w)

/-- Externalizing the full window-`6` history into finitely many additive registers is impossible. -/
def window6HistoryExternalizationNontrivial : Prop :=
  window6InfiniteRegisterBudget

/-- The explicit window-`6` audit example packages the concrete instantiation, visible two-sheet
structure, residual boundary obstruction, ledger split, audited spectrum, and history
externalization obstruction into one paper-facing statement.
    prop:typed-address-biaxial-completion-window6-auditable-example -/
theorem paper_typed_address_biaxial_completion_window6_auditable_example :
    window6AuditableInstantiationExists ∧
      window6VisibleLayerNontrivial ∧
      window6LocalGlobalObstructionNontrivial ∧
      window6LedgerBudgetSplitNontrivial ∧
      window6StatisticalSpectrumAuditable ∧
      window6HistoryExternalizationNontrivial := by
  have hInst := paper_typed_address_biaxial_completion_instantiation_extraction
    window6AuditableInstantiation
  rcases paper_typed_address_biaxial_completion_window6_explicit_fibers 0 with
    ⟨htail, h2, h3, h4, halias⟩
  rcases paper_typed_address_biaxial_completion_window6_boundary_holonomy with
    ⟨_, _, hResidualRank, _, hResidualCard⟩
  rcases paper_typed_address_biaxial_completion_window6_audit_budget_split with
    ⟨_, _, _, _, _, hReplay, hBoundary, hAnomaly, _, _, hExternal⟩
  rcases paper_typed_address_biaxial_completion_window6_two_hidden_channels with
    ⟨_, h34, _⟩
  exact ⟨hInst, ⟨htail, by simpa using halias⟩, ⟨hResidualRank, hResidualCard⟩,
    ⟨hReplay, hBoundary, hAnomaly⟩, ⟨h2, h3, h4, h34⟩, hExternal⟩

end Omega.TypedAddressBiaxialCompletion
