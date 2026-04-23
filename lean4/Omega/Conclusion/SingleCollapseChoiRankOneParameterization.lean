import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.QfoldChannelChoiRankEqualsQcollision

namespace Omega.Conclusion

open Omega.OperatorAlgebra

/-- Concrete single-collapse data: one distinguished output fiber may have size larger than `1`,
while every other fiber has size at most `1`. -/
structure conclusion_single_collapse_choi_rank_one_parameterization_Data
    (Omega X : Type*) [Fintype Omega] [Fintype X] where
  fold : Omega → X
  q : ℕ
  hq : 2 ≤ q
  distinguished : X
  largeFiberCard : ℕ
  distinguished_fiber_card :
    conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card fold distinguished =
      largeFiberCard
  other_fiber_card_le_one :
    ∀ x : X, x ≠ distinguished →
      conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card fold x ≤ 1

namespace conclusion_single_collapse_choi_rank_one_parameterization_Data

/-- The scalar `q`-collision package attached to the single-collapse fold. -/
noncomputable def conclusion_single_collapse_choi_rank_one_parameterization_qcollision_data
    {Omega X : Type*} [Fintype Omega] [Fintype X]
    (D : conclusion_single_collapse_choi_rank_one_parameterization_Data Omega X) :
    FoldQuantumChannelCollisionData :=
  conclusion_qfold_channel_choi_rank_equals_qcollision_data D.fold D.q

/-- Paper-facing closed form for the `q`-fold Choi rank in the single-collapse regime. -/
def conclusion_single_collapse_choi_rank_one_parameterization_formula
    {Omega X : Type*} [Fintype Omega] [Fintype X]
    (D : conclusion_single_collapse_choi_rank_one_parameterization_Data Omega X) : Prop :=
  let E := D.conclusion_single_collapse_choi_rank_one_parameterization_qcollision_data
  E.qCollisionProjectorRank =
    D.largeFiberCard ^ D.q + (Fintype.card Omega - D.largeFiberCard)

lemma conclusion_single_collapse_choi_rank_one_parameterization_other_fiber_pow_eq
    {Omega X : Type*} [Fintype Omega] [Fintype X]
    (D : conclusion_single_collapse_choi_rank_one_parameterization_Data Omega X)
    {x : X} (hx : x ≠ D.distinguished) :
    conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card D.fold x ^ D.q =
      conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card D.fold x := by
  have hle :
      conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card D.fold x ≤ 1 :=
    D.other_fiber_card_le_one x hx
  have hcases :
      conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card D.fold x = 0 ∨
        conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card D.fold x = 1 := by
    omega
  have hq_ne_zero : D.q ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) D.hq)
  rcases hcases with hzero | hone
  · simp [hzero, hq_ne_zero]
  · simp [hone]

end conclusion_single_collapse_choi_rank_one_parameterization_Data

open conclusion_single_collapse_choi_rank_one_parameterization_Data

/-- Paper label: `thm:conclusion-single-collapse-choi-rank-one-parameterization`. The existing
`q`-collision Choi-rank theorem reduces the Choi rank to the `q`-moment of the fiber sizes; in
the single-collapse regime this is exactly `t^q + (|Omega| - t)`. -/
theorem paper_conclusion_single_collapse_choi_rank_one_parameterization
    {Omega X : Type*} [Fintype Omega] [Fintype X]
    (D : conclusion_single_collapse_choi_rank_one_parameterization_Data Omega X) :
    D.conclusion_single_collapse_choi_rank_one_parameterization_formula := by
  classical
  let A : X → ℕ := conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card D.fold
  let E := D.conclusion_single_collapse_choi_rank_one_parameterization_qcollision_data
  let s : Finset X := (Finset.univ : Finset X).erase D.distinguished
  have hA_dist : A D.distinguished = D.largeFiberCard := by
    simpa [A] using D.distinguished_fiber_card
  have hA_dist_pow : A D.distinguished ^ D.q = D.largeFiberCard ^ D.q := by
    rw [hA_dist]
  have hverified :
      E.qCollisionProjectorRank = E.sqMoment := by
    exact
      (conclusion_qfold_channel_choi_rank_equals_qcollision_verified D.fold D.q D.hq).2
  have hrank :
      E.qCollisionProjectorRank = ∑ x : X, A x ^ D.q := by
    simpa [A, E,
      conclusion_single_collapse_choi_rank_one_parameterization_qcollision_data,
      conclusion_qfold_channel_choi_rank_equals_qcollision_data,
      conclusion_qfold_channel_choi_rank_equals_qcollision_block_ranks,
      conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card,
      FoldQuantumChannelCollisionData.sqMoment] using hverified
  have hsplit_q :
      (∑ x : X, A x ^ D.q) =
        A D.distinguished ^ D.q + s.sum (fun x => A x ^ D.q) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      ((Finset.sum_erase_add (s := (Finset.univ : Finset X))
        (f := fun x : X => A x ^ D.q) (by simp : D.distinguished ∈ (Finset.univ : Finset X))).symm)
  have hsplit_card :
      (∑ x : X, A x) =
        A D.distinguished + s.sum A := by
    simpa [add_comm, add_left_comm, add_assoc] using
      ((Finset.sum_erase_add (s := (Finset.univ : Finset X))
        (f := fun x : X => A x) (by simp : D.distinguished ∈ (Finset.univ : Finset X))).symm)
  have hother_q_eq :
      s.sum (fun x => A x ^ D.q) = s.sum A := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact D.conclusion_single_collapse_choi_rank_one_parameterization_other_fiber_pow_eq
      (by
        have : x ∈ (Finset.univ : Finset X).erase D.distinguished := by simpa [s] using hx
        simpa using (Finset.mem_erase.mp this).1)
  have hcardOmega :
      Fintype.card Omega = ∑ x : X, A x := by
    simpa [A, conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card] using
      (Fintype.sum_fiberwise (g := D.fold) (f := fun _ : Omega => (1 : ℕ))).symm
  have hother_card :
      s.sum A = Fintype.card Omega - D.largeFiberCard := by
    have hcard_split' :
        Fintype.card Omega = D.largeFiberCard + s.sum A := by
      calc
        Fintype.card Omega = ∑ x : X, A x := hcardOmega
        _ = A D.distinguished + s.sum A := hsplit_card
        _ = D.largeFiberCard + s.sum A := by
          rw [hA_dist]
    exact Nat.eq_sub_of_add_eq (by simpa [add_comm] using hcard_split'.symm)
  show E.qCollisionProjectorRank = D.largeFiberCard ^ D.q + (Fintype.card Omega - D.largeFiberCard)
  calc
    E.qCollisionProjectorRank = ∑ x : X, A x ^ D.q := hrank
    _ = D.largeFiberCard ^ D.q + s.sum A := by
      rw [hsplit_q, hA_dist_pow, hother_q_eq]
    _ = D.largeFiberCard ^ D.q + (Fintype.card Omega - D.largeFiberCard) := by
      rw [hother_card]

end Omega.Conclusion
