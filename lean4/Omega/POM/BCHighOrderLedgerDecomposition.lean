import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- One local fiber in a finite surjection chain, recorded by the inner composite fiber
cardinalities on a single `f_{i+1}`-fiber. -/
structure BCHighOrderLedgerStep where
  fiberCard : ℕ
  fiberCard_pos : 0 < fiberCard
  compositeFiberCard : Fin fiberCard → ℕ
  compositeFiberCard_pos : ∀ i, 0 < compositeFiberCard i

namespace BCHighOrderLedgerStep

/-- Total composite cardinality on the current outer fiber. -/
noncomputable def totalCompositeCard (S : BCHighOrderLedgerStep) : ℝ :=
  ∑ i, (S.compositeFiberCard i : ℝ)

lemma totalCompositeCard_pos (S : BCHighOrderLedgerStep) : 0 < S.totalCompositeCard := by
  let i0 : Fin S.fiberCard := ⟨0, S.fiberCard_pos⟩
  have hleNat : S.compositeFiberCard i0 ≤ ∑ i, S.compositeFiberCard i := by
    simpa using
      (Finset.single_le_sum
        (fun i _ => Nat.zero_le (S.compositeFiberCard i))
        (by simp : i0 ∈ (Finset.univ : Finset (Fin S.fiberCard))))
  have hle : (S.compositeFiberCard i0 : ℝ) ≤ S.totalCompositeCard := by
    unfold totalCompositeCard
    exact_mod_cast hleNat
  exact lt_of_lt_of_le (by exact_mod_cast S.compositeFiberCard_pos i0) hle

/-- Arithmetic mean of the incoming composite fiber cardinalities. -/
noncomputable def averageCompositeCard (S : BCHighOrderLedgerStep) : ℝ :=
  S.totalCompositeCard / (S.fiberCard : ℝ)

/-- Mean of the logarithms of the incoming composite fiber cardinalities. -/
noncomputable def averageLogCompositeCard (S : BCHighOrderLedgerStep) : ℝ :=
  (∑ i, Real.log (S.compositeFiberCard i : ℝ)) / (S.fiberCard : ℝ)

/-- Local AM-GM defect for the current outer fiber. -/
noncomputable def localAmgmDefect (S : BCHighOrderLedgerStep) : ℝ :=
  Real.log S.averageCompositeCard - S.averageLogCompositeCard

/-- The summand obtained by expanding the sequential/direct lift log-ratio before telescoping the
composite fiber-cardinality terms. -/
noncomputable def stageLedgerTerm (S : BCHighOrderLedgerStep) : ℝ :=
  Real.log S.totalCompositeCard - Real.log (S.fiberCard : ℝ) - S.averageLogCompositeCard

lemma stageLedgerTerm_eq_localAmgmDefect (S : BCHighOrderLedgerStep) :
    S.stageLedgerTerm = S.localAmgmDefect := by
  have hsum : S.totalCompositeCard ≠ 0 := ne_of_gt S.totalCompositeCard_pos
  have hcard : (S.fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt S.fiberCard_pos
  rw [stageLedgerTerm, localAmgmDefect, averageCompositeCard, averageLogCompositeCard]
  rw [Real.log_div hsum hcard]

end BCHighOrderLedgerStep

/-- Concrete finite chain data for the high-order Beck-Chevalley ledger: each stage records one
outer fiber together with the list of incoming composite fiber sizes that must be averaged on that
fiber. Summing the stage ledger terms models the sequential/direct lift KL defect, while summing
the local AM-GM defects models the local decomposition. -/
structure BCHighOrderLedgerData where
  depth : ℕ
  steps : Fin depth → BCHighOrderLedgerStep

namespace BCHighOrderLedgerData

/-- The KL defect after expanding the sequential/direct lift log-ratio stage by stage. -/
noncomputable def sequentialDirectLiftKlDefect (D : BCHighOrderLedgerData) : ℝ :=
  ∑ i, (D.steps i).stageLedgerTerm

/-- The sum of the local AM-GM defects along the whole chain. -/
noncomputable def localAmgmDefectSum (D : BCHighOrderLedgerData) : ℝ :=
  ∑ i, (D.steps i).localAmgmDefect

/-- High-order Beck-Chevalley ledger decomposition: the expanded KL defect telescopes to the sum
of local AM-GM defects. -/
def klDefectDecomposesAsLocalAmgmSum (D : BCHighOrderLedgerData) : Prop :=
  D.sequentialDirectLiftKlDefect = D.localAmgmDefectSum

end BCHighOrderLedgerData

/-- Paper-facing `k`-step Beck-Chevalley ledger package: after expanding the sequential/direct
lift log-ratio, each stage contributes the local AM-GM defect of the incoming composite
fiber-cardinality profile.
    thm:pom-bc-high-order-ledger-decomposition -/
theorem paper_pom_bc_high_order_ledger_decomposition (D : BCHighOrderLedgerData) :
    D.klDefectDecomposesAsLocalAmgmSum := by
  unfold BCHighOrderLedgerData.klDefectDecomposesAsLocalAmgmSum
    BCHighOrderLedgerData.sequentialDirectLiftKlDefect
    BCHighOrderLedgerData.localAmgmDefectSum
  simp [BCHighOrderLedgerStep.stageLedgerTerm_eq_localAmgmDefect]

end

end Omega.POM
