import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite data for the replica-softcore transfer package. The replica state space is the
Boolean cube `U_q = {0,1}^q`, the initial weight is an arbitrary nonnegative mass on `U_q`, and
the softcore transfer weight is the explicit overlap penalty `1` or `1/2`. -/
structure pom_multiplicity_composition_replica_softcore_transfer_data where
  q : ℕ
  paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass :
    (Fin q → Bool) → ℚ
  paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass_nonneg :
    ∀ u, 0 ≤
      paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u

namespace pom_multiplicity_composition_replica_softcore_transfer_data

/-- The finite replica state space `U_q = {0,1}^q`. -/
abbrev paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) :=
  Fin D.q → Bool

/-- The explicit softcore overlap count between two replica states. -/
def paper_label_pom_multiplicity_composition_replica_softcore_transfer_overlap
    (D : pom_multiplicity_composition_replica_softcore_transfer_data)
    (u v : D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state) :
    ℕ :=
  (Finset.univ.filter fun i : Fin D.q => u i && v i).card

/-- The transfer weight attached to one step of the replica-softcore chain. -/
def paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
    (D : pom_multiplicity_composition_replica_softcore_transfer_data)
    (u v : D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state) :
    ℚ :=
  if D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_overlap u v = 0 then
    1
  else
    1 / 2

/-- The finite-state transfer kernel iterated `n` times. This is the chapter-local matrix-power
entry used for the paper-facing formula. -/
def paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) :
    ℕ →
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state →
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state →
      ℚ
  | 0, u, v => if u = v then 1 else 0
  | n + 1, u, w =>
      ∑ v,
        paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power D n u v *
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v w

/-- The weighted multiplicity-composition mass at time `n`, indexed by the final replica state. -/
def paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) :
    ℕ →
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state →
      ℚ
  | 0, v =>
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass v
  | n + 1, v =>
      ∑ u,
        paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition D n u *
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v

/-- Total weighted mass after `n` transfer steps. -/
def paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) (n : ℕ) : ℚ :=
  ∑ v, D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition n v

/-- The crude Perron-Frobenius proxy coming from the size of the explicit state space. -/
def paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) : ℚ :=
  2 ^ D.q

/-- Paper-facing package: the weighted compositions satisfy the cut-set recursion, the same
quantities equal the transfer-kernel power applied to the initial mass, and the total mass grows
at most exponentially with base `|U_q| = 2^q`. -/
def pom_multiplicity_composition_replica_softcore_transfer_statement
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) : Prop :=
  (∀ n v,
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
          (n + 1) v =
        ∑ u,
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
              n u *
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v) ∧
    (∀ n v,
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
          n v =
        ∑ u,
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
              n u v) ∧
    ∀ n,
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass n ≤
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound ^ n *
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass 0

lemma paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_nonneg
    (D : pom_multiplicity_composition_replica_softcore_transfer_data)
    (u v : D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state) :
    0 ≤ D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v := by
  unfold paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
  split_ifs <;> norm_num

lemma paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_le_one
    (D : pom_multiplicity_composition_replica_softcore_transfer_data)
    (u v : D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state) :
    D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v ≤ 1 := by
  unfold paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
  split_ifs <;> norm_num

lemma paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition_nonneg
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) :
    ∀ n v,
      0 ≤
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition n v
  | 0, v =>
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass_nonneg v
  | n + 1, v => by
      dsimp [paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition]
      refine Finset.sum_nonneg ?_
      intro u hu
      exact mul_nonneg
        (paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition_nonneg
          D n u)
        (paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_nonneg D u v)

lemma paper_label_pom_multiplicity_composition_replica_softcore_transfer_row_sum_le_perron_bound
    (D : pom_multiplicity_composition_replica_softcore_transfer_data)
    (u : D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state) :
    (∑ v,
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v) ≤
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound := by
  have hsum_le :
      (∑ v,
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v) ≤
        ∑ _v :
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_replica_state,
          (1 : ℚ) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_le_one D u v
  simpa [paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound] using
    hsum_le

lemma paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition_eq
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) :
    ∀ n v,
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition n v =
        ∑ u,
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
              n u v
  | 0, v => by
      simp [paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition,
        paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power]
  | n + 1, w => by
      calc
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
            (n + 1) w =
          ∑ v,
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
                n v *
              D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v w := by
                rfl
        _ =
          ∑ v,
            (∑ u,
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
                  D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                    n u v) *
              D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v w := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                rw [paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition_eq
                  D n v]
        _ =
          ∑ v,
            ∑ u,
              D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                  n u v *
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v w := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                calc
                  (∑ u,
                      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                          n u v) *
                    D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v
                      w =
                    ∑ u,
                      (D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass
                          u *
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                          n u v) *
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
                          v w := by
                            rw [Finset.sum_mul]
                  _ =
                    ∑ u,
                      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass
                          u *
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                          n u v *
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
                          v w := by
                            refine Finset.sum_congr rfl ?_
                            intro u hu
                            ring
        _ =
          ∑ u,
            ∑ v,
              D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                  n u v *
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v w := by
                rw [Finset.sum_comm]
        _ =
          ∑ u,
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
              ∑ v,
                  D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                    n u v *
                  D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer v w := by
                refine Finset.sum_congr rfl ?_
                intro u hu
                have hfactor :
                    (∑ v,
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass
                            u *
                          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                            n u v *
                          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
                            v w) =
                      ∑ v,
                        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass
                            u *
                          (D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                              n u v *
                            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer
                              v w) := by
                      refine Finset.sum_congr rfl ?_
                      intro v hv
                      ring
                rw [hfactor, Finset.mul_sum]
        _ =
          ∑ u,
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass u *
              D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer_power
                (n + 1) u w := by
                rfl

lemma paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass_step
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) (n : ℕ) :
    D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass (n + 1) ≤
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound *
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass n := by
  calc
    D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass (n + 1) =
      ∑ v,
        ∑ u,
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
              n u *
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v := by
              rfl
    _ =
      ∑ u,
        ∑ v,
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
              n u *
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v := by
              rw [Finset.sum_comm]
    _ =
      ∑ u,
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
            n u *
          ∑ v, D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_transfer u v := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            rw [← Finset.mul_sum]
    _ ≤
      ∑ u,
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition
            n u *
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound := by
            refine Finset.sum_le_sum ?_
            intro u hu
            exact mul_le_mul_of_nonneg_left
              (paper_label_pom_multiplicity_composition_replica_softcore_transfer_row_sum_le_perron_bound
                D u)
              (paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition_nonneg
                D n u)
    _ =
      D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound *
        D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass n := by
          symm
          unfold paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro u hu
          ring

end pom_multiplicity_composition_replica_softcore_transfer_data

open pom_multiplicity_composition_replica_softcore_transfer_data

/-- Paper label: `prop:pom-multiplicity-composition-replica-softcore-transfer`. The explicit
replica-softcore state space is the Boolean cube `U_q`, the weighted compositions satisfy the
cut-set recursion, the same quantities are the transfer-kernel powers applied to the initial mass,
and the total mass therefore has the expected finite-state exponential growth bound. -/
theorem paper_pom_multiplicity_composition_replica_softcore_transfer
    (D : pom_multiplicity_composition_replica_softcore_transfer_data) :
    D.pom_multiplicity_composition_replica_softcore_transfer_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n v
    rfl
  · exact D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_weightedComposition_eq
  · intro n
    induction n with
    | zero =>
        simp [paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass]
    | succ n ih =>
        have hperron_nonneg :
            0 ≤ D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound := by
          unfold paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound
          positivity
        calc
          D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass (n + 1) ≤
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound *
              D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass n := by
                simpa [Nat.add_comm] using
                  D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass_step n
          _ ≤
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound *
              (D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound ^ n *
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass 0) := by
                  exact mul_le_mul_of_nonneg_left ih hperron_nonneg
          _ =
            D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_perron_bound ^
              (n + 1) *
                D.paper_label_pom_multiplicity_composition_replica_softcore_transfer_totalMass 0 := by
                  simp [pow_succ, mul_assoc, mul_comm]

end Omega.POM
