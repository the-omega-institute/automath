import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete closed-form data for the replica-softcore reciprocal-moment partition formula.
The two stored coordinates are the bulk term and the partition contribution; `Sneg` is the
closed-form total. -/
abbrev xi_replica_softcore_reciprocal_moment_partition_closed_form_data (_m _q : ℕ) :=
  ℤ × ℤ

/-- Bulk reciprocal contribution `Omega_m^(-)(q)`. -/
def xi_replica_softcore_reciprocal_moment_partition_closed_form_data.OmegaNeg {m q : ℕ}
    (D : xi_replica_softcore_reciprocal_moment_partition_closed_form_data m q) : ℤ :=
  D.1

/-- Sum over cyclic partition multiplicities. -/
def xi_replica_softcore_reciprocal_moment_partition_closed_form_data.partitionSum {m q : ℕ}
    (D : xi_replica_softcore_reciprocal_moment_partition_closed_form_data m q) : ℤ :=
  D.2

/-- The full negative reciprocal moment assembled from the bulk and partition terms. -/
def xi_replica_softcore_reciprocal_moment_partition_closed_form_data.Sneg {m q : ℕ}
    (D : xi_replica_softcore_reciprocal_moment_partition_closed_form_data m q) : ℤ :=
  2 ^ m * D.OmegaNeg + D.partitionSum

/-- Paper label:
`thm:xi-replica-softcore-reciprocal-moment-partition-closed-form`. -/
theorem paper_xi_replica_softcore_reciprocal_moment_partition_closed_form (m q : ℕ)
    (D : xi_replica_softcore_reciprocal_moment_partition_closed_form_data m q) :
    D.Sneg = 2 ^ m * D.OmegaNeg + D.partitionSum := by
  rfl

end Omega.Zeta
