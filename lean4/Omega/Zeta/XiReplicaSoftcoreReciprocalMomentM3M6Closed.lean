import Mathlib.Tactic
import Omega.Zeta.XiReplicaSoftcoreReciprocalMomentPartitionClosedForm

namespace Omega.Zeta

/-- Concrete data for the closed reciprocal moments at `m = 3, 4, 5, 6`.  Each component is the
corresponding specialization of the partition closed form, together with the finite partition sum
identity obtained by enumerating the surviving partition types. -/
structure xi_replica_softcore_reciprocal_moment_m3_m6_closed_data (q : ℕ) where
  m3 : xi_replica_softcore_reciprocal_moment_partition_closed_form_data 3 q
  m4 : xi_replica_softcore_reciprocal_moment_partition_closed_form_data 4 q
  m5 : xi_replica_softcore_reciprocal_moment_partition_closed_form_data 5 q
  m6 : xi_replica_softcore_reciprocal_moment_partition_closed_form_data 6 q
  partition_m3 : m3.partitionSum = -13
  partition_m4 : m4.partitionSum = -32 * (-1 : ℤ) ^ q + 17
  partition_m5 : m5.partitionSum = -80 * (2 : ℤ) ^ q + 40 * (-1 : ℤ) ^ q - 21
  partition_m6 : m6.partitionSum =
    96 * (2 : ℤ) ^ q - 192 * (-1 : ℤ) ^ q * (3 : ℤ) ^ q -
      48 * (-1 : ℤ) ^ q + 73

/-- The four boxed closed forms for the negative reciprocal moments. -/
def xi_replica_softcore_reciprocal_moment_m3_m6_closed_holds
    (q : ℕ) (D : xi_replica_softcore_reciprocal_moment_m3_m6_closed_data q) : Prop :=
  D.m3.Sneg = 8 * D.m3.OmegaNeg - 13 ∧
    D.m4.Sneg = 16 * D.m4.OmegaNeg - 32 * (-1 : ℤ) ^ q + 17 ∧
    D.m5.Sneg = 32 * D.m5.OmegaNeg - 80 * (2 : ℤ) ^ q + 40 * (-1 : ℤ) ^ q - 21 ∧
    D.m6.Sneg =
      64 * D.m6.OmegaNeg + 96 * (2 : ℤ) ^ q -
        192 * (-1 : ℤ) ^ q * (3 : ℤ) ^ q - 48 * (-1 : ℤ) ^ q + 73

/-- Paper label: `cor:xi-replica-softcore-reciprocal-moment-m3-m6-closed`. -/
theorem paper_xi_replica_softcore_reciprocal_moment_m3_m6_closed
    (q : ℕ) (hq : 2 ≤ q) (D : xi_replica_softcore_reciprocal_moment_m3_m6_closed_data q) :
    xi_replica_softcore_reciprocal_moment_m3_m6_closed_holds q D := by
  have hq_nonneg : 0 ≤ q := le_trans (by norm_num) hq
  clear hq_nonneg
  have h3 := paper_xi_replica_softcore_reciprocal_moment_partition_closed_form 3 q D.m3
  have h4 := paper_xi_replica_softcore_reciprocal_moment_partition_closed_form 4 q D.m4
  have h5 := paper_xi_replica_softcore_reciprocal_moment_partition_closed_form 5 q D.m5
  have h6 := paper_xi_replica_softcore_reciprocal_moment_partition_closed_form 6 q D.m6
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h3, D.partition_m3]
    ring
  · rw [h4, D.partition_m4]
    ring
  · rw [h5, D.partition_m5]
    ring
  · rw [h6, D.partition_m6]
    ring

end Omega.Zeta
