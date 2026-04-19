import Omega.GU.CongruenceM6IdempotentsFourRegistered
import Omega.GU.Window6LowrankNeedsObservableCompression

namespace Omega.GU

open Submodule

/-- Concrete window-6 rational observable-compression data. The ambient observable envelope is a
`ℚ`-submodule, and the existing low-rank rigidity theorem forces it to be top. -/
structure TerminalWindow6RationalObservableCompressionData where
  V : Type*
  instAddCommGroup : AddCommGroup V
  instModule : Module ℚ V
  bracket : V → V → V
  generators : Submodule ℚ V
  ambient : Submodule ℚ V
  generators_le_ambient : generators ≤ ambient
  ambient_bracketClosed : BracketClosed bracket ambient
  lieClosure_top :
    ∀ lieClosure : Submodule ℚ V,
      generators ≤ lieClosure → BracketClosed bracket lieClosure →
        (∀ W : Submodule ℚ V,
          generators ≤ W → BracketClosed bracket W → lieClosure ≤ W) →
          lieClosure = ⊤

namespace TerminalWindow6RationalObservableCompressionData

/-- Window 6 has exactly four rational idempotents, and any low-rank observable compression
compatible with the bracket closure is forced to be trivial. -/
def observableCompressionTriviality (D : TerminalWindow6RationalObservableCompressionData) : Prop :=
  Omega.GU.CongruenceM6IdempotentsFour.idem21.card = 4 ∧ D.ambient = ⊤

end TerminalWindow6RationalObservableCompressionData

open TerminalWindow6RationalObservableCompressionData

theorem paper_terminal_window6_rational_observable_compression_triviality
    (D : TerminalWindow6RationalObservableCompressionData) : D.observableCompressionTriviality := by
  letI := D.instAddCommGroup
  letI := D.instModule
  refine ⟨paper_congruence_m6_idempotents_four_registered_seeds, ?_⟩
  exact paper_window6_lowrank_needs_observable_compression D.bracket D.generators D.ambient
    D.generators_le_ambient D.ambient_bracketClosed D.lieClosure_top

end Omega.GU
