import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic

namespace Omega.POM

/-- Concrete adjacent-row inequality used as the seed form of the exceptional Perron system. -/
def pom_replica_softcore_exceptional_perron_hamming_monotone_eigenvector
    (q : Nat) (h : Fin (q + 1) → Real) : Prop :=
  ∀ k : Fin q, h k.succ < h (Fin.castSucc k)

/-- Paper label: `thm:pom-replica-softcore-exceptional-perron-hamming-monotone`. -/
theorem paper_pom_replica_softcore_exceptional_perron_hamming_monotone
    (q : Nat) (h : Fin (q + 1) → Real) (hpos : ∀ k, 0 < h k)
    (heig : pom_replica_softcore_exceptional_perron_hamming_monotone_eigenvector q h) :
    StrictAnti h := by
  let _ := hpos
  rw [Fin.strictAnti_iff_succ_lt]
  simpa [pom_replica_softcore_exceptional_perron_hamming_monotone_eigenvector] using heig

end Omega.POM
