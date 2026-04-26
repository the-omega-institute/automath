import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete fiber-multiplicity data for the genus Hausdorff moment sequence package. -/
structure conclusion_tqft_genus_hausdorff_moment_sequence_data where
  n : ℕ
  conclusion_tqft_genus_hausdorff_moment_sequence_dm : Fin n → ℕ
  conclusion_tqft_genus_hausdorff_moment_sequence_dm_pos :
    ∀ x, 1 ≤ conclusion_tqft_genus_hausdorff_moment_sequence_dm x
  conclusion_tqft_genus_hausdorff_moment_sequence_nonempty : 0 < n

namespace conclusion_tqft_genus_hausdorff_moment_sequence_data

/-- The atomic node `d_m(x)^{-2}` attached to a visible fiber. -/
noncomputable def conclusion_tqft_genus_hausdorff_moment_sequence_node
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) (x : Fin D.n) : ℝ :=
  1 / (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) ^ 2

/-- Uniform atomic weights on the finite visible layer `X_m`. -/
noncomputable def conclusion_tqft_genus_hausdorff_moment_sequence_weight
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) : ℝ :=
  1 / D.n

/-- The normalized genus partition function `Z_m(Σ_(g+1)) / |X_m|`. -/
noncomputable def conclusion_tqft_genus_hausdorff_moment_sequence_partition
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) (g : ℕ) : ℝ :=
  (∑ x : Fin D.n, D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ g) / D.n

/-- The corresponding atomic Hausdorff moment. -/
noncomputable def conclusion_tqft_genus_hausdorff_moment_sequence_atomic_moment
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) (g : ℕ) : ℝ :=
  ∑ x : Fin D.n,
    D.conclusion_tqft_genus_hausdorff_moment_sequence_weight *
      D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ g

/-- The normalized genus tower is the Hausdorff moment sequence of the atomic measure on
`d_m(x)^{-2}`. -/
def conclusion_tqft_genus_hausdorff_moment_sequence_moment_representation
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) : Prop :=
  ∀ g : ℕ,
    D.conclusion_tqft_genus_hausdorff_moment_sequence_partition g =
      D.conclusion_tqft_genus_hausdorff_moment_sequence_atomic_moment g

/-- Hausdorff complete monotonicity for the normalized genus tower. -/
def conclusion_tqft_genus_hausdorff_moment_sequence_complete_monotonicity
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) : Prop :=
  ∀ g k : ℕ,
    0 ≤
      ∑ x : Fin D.n,
        D.conclusion_tqft_genus_hausdorff_moment_sequence_weight *
          D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ g *
            (1 - D.conclusion_tqft_genus_hausdorff_moment_sequence_node x) ^ k

/-- Hankel positivity for the Hausdorff moment sequence. -/
def conclusion_tqft_genus_hausdorff_moment_sequence_hankel_positivity
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) : Prop :=
  ∀ g m : ℕ, ∀ c : Fin m → ℝ,
    0 ≤
      ∑ x : Fin D.n,
        D.conclusion_tqft_genus_hausdorff_moment_sequence_weight *
          D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ g *
            (∑ i : Fin m,
                c i * D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ (i : ℕ)) ^ 2

end conclusion_tqft_genus_hausdorff_moment_sequence_data

private lemma conclusion_tqft_genus_hausdorff_moment_sequence_node_nonneg
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) (x : Fin D.n) :
    0 ≤ D.conclusion_tqft_genus_hausdorff_moment_sequence_node x := by
  have h :
      0 ≤ 1 / (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) ^ 2 := by
    positivity
  simpa [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_node] using h

private lemma conclusion_tqft_genus_hausdorff_moment_sequence_node_le_one
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) (x : Fin D.n) :
    D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ≤ 1 := by
  let t : ℝ := (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) ^ 2
  have ht_pos : 0 < t := by
    have hdm_pos : (0 : ℝ) < D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x := by
      exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_dm_pos x
    dsimp [t]
    nlinarith
  have hdm_ge : (1 : ℝ) ≤ D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x := by
    exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_dm_pos x
  have ht_ge : (1 : ℝ) ≤ t := by
    dsimp [t]
    nlinarith
  calc
    D.conclusion_tqft_genus_hausdorff_moment_sequence_node x = 1 / t := by
      simp [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_node, t]
    _ ≤ 1 := by
      simpa using
        (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) ht_ge)

/-- Paper label: `thm:conclusion-tqft-genus-hausdorff-moment-sequence`. -/
theorem paper_conclusion_tqft_genus_hausdorff_moment_sequence
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) :
    D.conclusion_tqft_genus_hausdorff_moment_sequence_moment_representation ∧
      D.conclusion_tqft_genus_hausdorff_moment_sequence_complete_monotonicity ∧
      D.conclusion_tqft_genus_hausdorff_moment_sequence_hankel_positivity := by
  refine ⟨?_, ?_, ?_⟩
  · intro g
    simp [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_partition,
      conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_atomic_moment,
      conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_weight,
      div_eq_mul_inv, Finset.mul_sum, mul_comm]
  · intro g k
    refine Finset.sum_nonneg ?_
    intro x hx
    have hweight_nonneg :
        0 ≤ D.conclusion_tqft_genus_hausdorff_moment_sequence_weight := by
      have h : 0 ≤ (1 / (D.n : ℝ)) := by positivity
      simpa [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_weight] using h
    have hnode_nonneg :
        0 ≤ D.conclusion_tqft_genus_hausdorff_moment_sequence_node x :=
      conclusion_tqft_genus_hausdorff_moment_sequence_node_nonneg D x
    have htail_nonneg :
        0 ≤ 1 - D.conclusion_tqft_genus_hausdorff_moment_sequence_node x := by
      have hnode_le := conclusion_tqft_genus_hausdorff_moment_sequence_node_le_one D x
      linarith
    exact mul_nonneg
      (mul_nonneg hweight_nonneg (pow_nonneg hnode_nonneg g))
      (pow_nonneg htail_nonneg k)
  · intro g m c
    refine Finset.sum_nonneg ?_
    intro x hx
    have hweight_nonneg :
        0 ≤ D.conclusion_tqft_genus_hausdorff_moment_sequence_weight := by
      have h : 0 ≤ (1 / (D.n : ℝ)) := by positivity
      simpa [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_weight] using h
    have hnode_nonneg :
        0 ≤ D.conclusion_tqft_genus_hausdorff_moment_sequence_node x :=
      conclusion_tqft_genus_hausdorff_moment_sequence_node_nonneg D x
    exact mul_nonneg
      (mul_nonneg hweight_nonneg (pow_nonneg hnode_nonneg g))
      (sq_nonneg _)

end Omega.Conclusion
