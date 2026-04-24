import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Omega.POM

/-- The number of independent vertex subsets of a finite graph. -/
noncomputable def independentSetCount {V : Type} (Γ : SimpleGraph V) [Fintype V] [DecidableEq V] :
    Nat := by
  let _ : DecidableRel Γ.Adj := Classical.decRel _
  exact Fintype.card {s : Finset V // Γ.IsIndepSet (s : Set V)}

/-- The number of `q`-label target maps, encoded here as `q` independent-set choices. -/
noncomputable def disjointTargetHomCount {V : Type} (Γ : SimpleGraph V) [Fintype V]
    [DecidableEq V] (q : Nat) : Nat := by
  let _ : DecidableRel Γ.Adj := Classical.decRel _
  exact Fintype.card (Fin q → {s : Finset V // Γ.IsIndepSet (s : Set V)})

/-- Paper label: `prop:pom-indset-power-hom-disj`. -/
theorem paper_pom_indset_power_hom_disj {V : Type} (Γ : SimpleGraph V) [Fintype V] [DecidableEq V]
    (q : Nat) : independentSetCount Γ ^ q = disjointTargetHomCount Γ q := by
  classical
  simp [independentSetCount, disjointTargetHomCount]

end Omega.POM
