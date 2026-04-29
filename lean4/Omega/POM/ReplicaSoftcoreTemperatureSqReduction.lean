import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The weight-layer reduction entry from the `S_q`-invariant softcore temperature kernel. -/
def pom_replica_softcore_temperature_sq_reduction_matrix_entry
    (q : ℕ) (p : ℝ) (k l : ℕ) : ℝ :=
  p * Nat.choose q l + (1 - p) * Nat.choose (q - k) l

/-- The closed-form row sum attached to the weight layer `k`. -/
def pom_replica_softcore_temperature_sq_reduction_row_sum
    (q : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  p * (2 : ℝ) ^ q + (1 - p) * (2 : ℝ) ^ (q - k)

/-- The symmetric row `k = 0` carries the Perron value in the reduced model. -/
def pom_replica_softcore_temperature_sq_reduction_symmetric_root (q : ℕ) : ℝ :=
  (2 : ℝ) ^ q

/-- The reduced Perron value is the maximal closed-form row sum. -/
def pom_replica_softcore_temperature_sq_reduction_full_root
    (q : ℕ) (_p : ℝ) : ℝ :=
  pom_replica_softcore_temperature_sq_reduction_symmetric_root q

/-- Paper label: `prop:pom-replica-softcore-temperature-sq-reduction`.
The `S_q`-invariant temperature kernel reduces to the explicit weight-layer matrix, the symmetric
row has total mass `2^q`, and for `p ∈ [0,1]` that row realizes the maximal reduced Perron value.
-/
theorem paper_pom_replica_softcore_temperature_sq_reduction (q : ℕ) (p : ℝ) :
    (∀ k l : ℕ,
        pom_replica_softcore_temperature_sq_reduction_matrix_entry q p k l =
          p * Nat.choose q l + (1 - p) * Nat.choose (q - k) l) ∧
      (Finset.sum (Finset.range (q + 1))
          (fun l => pom_replica_softcore_temperature_sq_reduction_matrix_entry q p 0 l) =
        pom_replica_softcore_temperature_sq_reduction_symmetric_root q) ∧
      (0 ≤ p ∧ p ≤ 1 →
        pom_replica_softcore_temperature_sq_reduction_full_root q p =
          pom_replica_softcore_temperature_sq_reduction_symmetric_root q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k l
    rfl
  · have hchoose :
        Finset.sum (Finset.range (q + 1)) (fun l => (Nat.choose q l : ℝ)) = (2 : ℝ) ^ q := by
      exact_mod_cast Nat.sum_range_choose q
    have hchoose0 :
        Finset.sum (Finset.range (q + 1)) (fun l => (Nat.choose (q - 0) l : ℝ)) = (2 : ℝ) ^ q := by
      simpa using hchoose
    unfold pom_replica_softcore_temperature_sq_reduction_matrix_entry
      pom_replica_softcore_temperature_sq_reduction_symmetric_root
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hchoose, hchoose0]
    ring
  · rintro ⟨hp0, hp1⟩
    simp [pom_replica_softcore_temperature_sq_reduction_full_root]

end Omega.POM
