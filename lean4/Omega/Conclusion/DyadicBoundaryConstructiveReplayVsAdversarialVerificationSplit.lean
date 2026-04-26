import Mathlib.Tactic
import Omega.Conclusion.BoundaryGodelSyndromeCompletenessLinearDecode
import Omega.Conclusion.DyadicBoundaryGodelCodeParametersAndCheckRank
import Omega.Conclusion.DyadicBoundaryPathConsistencyQueryRankEqualsCheckRank

namespace Omega.Conclusion

/-- Concrete data for the replay-versus-verification split on the dyadic boundary model. The
replay side is witnessed by explicit boundary maps and a decoder, while the verification side is
measured by the closed-form check rank `H_{m,n}`. -/
structure conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data where
  m : ℕ
  n : ℕ
  p : ℕ
  two_le_n : 2 ≤ n
  Cn : Type
  Cn1 : Type
  Cn2 : Type
  Syndrome : Type
  instAddGroupCn : AddGroup Cn
  instAddGroupCn1 : AddGroup Cn1
  instAddGroupCn2 : AddGroup Cn2
  instAddGroupSyndrome : AddGroup Syndrome
  boundaryTop : Cn → Cn1
  boundaryLower : Cn1 → Cn2
  syndrome : Cn1 → Syndrome
  decodeFromBoundary : Cn1 → Cn
  work : Cn1 → Nat
  vertexCount : Nat
  edgeCount : Nat
  syndrome_exact : ∀ b, syndrome b = 0 ↔ boundaryLower b = 0
  boundary_chain : ∀ x, boundaryLower (boundaryTop x) = 0
  exact_fill : ∀ b, boundaryLower b = 0 → ∃ x, boundaryTop x = b
  boundary_sub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v
  boundary_ker : ∀ u, boundaryTop u = 0 → u = 0
  decode_exact : ∀ b, boundaryTop (decodeFromBoundary b) = b
  linear_work : ∀ b, work b ≤ vertexCount + edgeCount

attribute [instance]
  conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data.instAddGroupCn
  conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data.instAddGroupCn1
  conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data.instAddGroupCn2
  conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data.instAddGroupSyndrome

namespace conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data

/-- The committed replay problem is solved by a unique linear-time bulk decode. -/
def linear_replay
    (D : conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data) :
    Prop :=
  ∀ b, D.syndrome b = 0 → ∃! x, D.boundaryTop x = b ∧ D.work b ≤ D.vertexCount + D.edgeCount

/-- The adversarial query problem has lower bound exactly equal to the closed-form check rank. -/
def query_lower_bound
    (D : conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data) :
    Prop :=
  conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_queryRank D.m D.n D.p =
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank D.m D.n

/-- For `n ≥ 2`, the check rank already contains a full `2^(mn)` term, which is the concrete
asymptotic gap used in the paper-level comparison. -/
def asymptotic_gap
    (D : conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data) :
    Prop :=
  2 ^ (D.m * D.n) ≤
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank D.m D.n

end conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data

open conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data

/-- Paper label:
`thm:conclusion-dyadic-boundary-constructive-replay-vs-adversarial-verification-split`. -/
theorem paper_conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split
    (D : conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data) :
    D.linear_replay ∧ D.query_lower_bound ∧ D.asymptotic_gap := by
  have hReplay :=
    paper_conclusion_boundary_godel_syndrome_completeness_linear_decode D.boundaryTop
      D.boundaryLower D.syndrome D.decodeFromBoundary D.work D.vertexCount D.edgeCount
      D.syndrome_exact D.boundary_chain D.exact_fill D.boundary_sub D.boundary_ker
      D.decode_exact D.linear_work
  have hn : 0 < D.n := lt_of_lt_of_le (by decide : 0 < 2) D.two_le_n
  have hQuery :=
    paper_conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank D.m D.n D.p hn
  have hClosed := (paper_conclusion_dyadic_boundary_godel_code_parameters_and_check_rank D.m D.n).2.2
  refine ⟨?_, hQuery.2, ?_⟩
  · intro b hb
    exact (hReplay b).2 hb
  · unfold conclusion_dyadic_boundary_constructive_replay_vs_adversarial_verification_split_data.asymptotic_gap
    rw [hClosed]
    have hOne : 1 ≤ D.n - 1 := by
      exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) D.two_le_n))
    have hScaled : 2 ^ (D.m * D.n) ≤ (D.n - 1) * 2 ^ (D.m * D.n) := by
      simpa using Nat.mul_le_mul_right (2 ^ (D.m * D.n)) hOne
    exact hScaled.trans (Nat.le_add_right _ _)

end Omega.Conclusion
