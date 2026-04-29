import Omega.Combinatorics.PathIndSet
import Omega.Zeta.XiFoldFiberSquarefreePrimeExternalization
import Omega.Zeta.XiSquarefreePrimeSupportMinGrowth

namespace Omega.Zeta

/-- The canonical zero-slack support-growth datum used for the externalization overhead wrapper. -/
def xi_squarefree_externalization_log_overhead_support_data
    (m : Nat) : XiSquarefreePrimeSupportMinGrowthData m where
  supportSlack := 0

/-- Lower envelope for the coarse code-length support requirement. -/
def xi_squarefree_externalization_log_overhead_lower_envelope (m T : Nat) : Nat :=
  xiSquarefreePrimeSupportLowerEnvelope m T

/-- Explicit primorial support witness that dominates the lower envelope. -/
def xi_squarefree_externalization_log_overhead_support_witness (m T : Nat) : Nat :=
  (xi_squarefree_externalization_log_overhead_support_data m).supportWitness T

/-- A path component of size `2s+1` has an independent-set witness of size at least `s+1`. -/
def xi_squarefree_externalization_log_overhead_path_witness (s : Nat) : Prop :=
  ∃ S : Finset (Fin (2 * s + 1)),
    Omega.IsPathIndependent (2 * s + 1) S ∧ s + 1 ≤ S.card

/-- Concrete statement of the squarefree externalization logarithmic overhead package. -/
def xi_squarefree_externalization_log_overhead_statement : Prop :=
  (∀ m : Nat, Function.Injective (Omega.GroupUnification.foldPsi m)) ∧
  (∀ m : Nat, ∀ᶠ T in Filter.atTop,
    xi_squarefree_externalization_log_overhead_lower_envelope m T ≤
      xi_squarefree_externalization_log_overhead_support_witness m T) ∧
  (∀ s : Nat, xi_squarefree_externalization_log_overhead_path_witness s)

/-- Paper-facing wrapper for the squarefree-prime externalization overhead.
    cor:xi-squarefree-externalization-log-overhead -/
theorem paper_xi_squarefree_externalization_log_overhead :
    xi_squarefree_externalization_log_overhead_statement := by
  refine ⟨?_, ?_, ?_⟩
  · exact (paper_xi_fold_fiber_squarefree_prime_externalization).1
  · intro m
    change (xi_squarefree_externalization_log_overhead_support_data m).minGrowthEventually
    exact paper_xi_squarefree_prime_support_min_growth m
      (xi_squarefree_externalization_log_overhead_support_data m)
  · intro s
    obtain ⟨S, hS, hcard⟩ := Omega.pathIndSet_exists_max (2 * s + 1) (by omega)
    refine ⟨S, hS, ?_⟩
    rw [hcard]
    omega

end Omega.Zeta
