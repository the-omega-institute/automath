import Mathlib.Tactic

namespace Omega.POM

/-- The three audited Hausdorff atoms for the holding-interval tail law. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 : ℚ := 1 / 3
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 : ℚ := 1 / 4
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 : ℚ := 1 / 7

/-- Their atomic weights, normalized so that the tail at `m = 0` is exactly `1`. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 : ℚ := 1 / 2
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 : ℚ := 1 / 3
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 : ℚ := 1 / 6

/-- The complementary refresh probabilities `1 - κ / t_x`. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r0 : ℚ := 2 / 3
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r1 : ℚ := 3 / 4
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r2 : ℚ := 6 / 7

/-- The audited PGF in partial-fraction form. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_pgf (s : ℚ) : ℚ :=
  s / (3 - s) + s / (4 - s) + s / (7 - s)

/-- The finite polynomial `P_δ(z) = (3 - z) (4 - z) (7 - z)`. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta (z : ℚ) : ℚ :=
  84 - 61 * z + 14 * z ^ 2 - z ^ 3

/-- The explicit derivative of `P_δ`. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_PdeltaDeriv (z : ℚ) : ℚ :=
  -61 + 28 * z - 3 * z ^ 2

/-- The tail sequence `m ↦ P(H > m)` as a finite Hausdorff moment sequence. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_tail (m : ℕ) : ℚ :=
  pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ^ m +
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ^ m +
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ^ m

/-- The explicit complete-monotonicity witness `Σ_x π_x λ_x^m (1 - λ_x)^k`. -/
def pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_completeMonotoneWitness
    (k m : ℕ) : ℚ :=
  pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ^ m *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r0 ^ k +
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ^ m *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r1 ^ k +
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ^ m *
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r2 ^ k

lemma pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta_factor (z : ℚ) :
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta z =
      (3 - z) * (4 - z) * (7 - z) := by
  unfold pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta
  ring

/-- Paper label: `prop:pom-diagonal-rate-refresh-holding-interval-pgf-hausdorff`. The audited
three-atom refresh model has an explicit rational PGF, the same PGF is the logarithmic
derivative of `P_δ`, and the tail law is a finite Hausdorff moment sequence with an explicit
complete-monotonicity witness. -/
theorem paper_pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff
    (s : ℚ) (h3 : s ≠ 3) (h4 : s ≠ 4) (h7 : s ≠ 7) :
    pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_pgf s =
      -s * pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_PdeltaDeriv s /
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta s ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_tail 0 = 1 ∧
      (∀ m,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_tail m =
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 *
              pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ^ m +
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 *
              pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ^ m +
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 *
              pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ^ m) ∧
      0 ≤ pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 < 1 ∧
      0 ≤ pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 < 1 ∧
      0 ≤ pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ∧
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 < 1 ∧
      0 < pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 ∧
      0 < pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 ∧
      0 < pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 ∧
      (∀ k m,
        0 ≤
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_completeMonotoneWitness k m) := by
  have h3' : 3 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h3)
  have h4' : 4 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h4)
  have h7' : 7 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h7)
  have hP :
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta s ≠ 0 := by
    rw [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta_factor]
    exact mul_ne_zero (mul_ne_zero h3' h4') h7'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_pgf
    unfold pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_PdeltaDeriv
    rw [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_Pdelta_factor]
    field_simp [h3', h4', h7', hP]
    ring
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_tail,
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0,
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1,
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2,
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0,
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1,
      pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2]
  · intro m
    rfl
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1]
  · norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2]
  · intro k m
    have h0 :
        0 ≤
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0 *
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0 ^ m *
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r0 ^ k := by
      norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w0,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node0,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r0]
    have h1 :
        0 ≤
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1 *
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1 ^ m *
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r1 ^ k := by
      norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w1,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node1,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r1]
    have h2 :
        0 ≤
          pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2 *
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2 ^ m *
            pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r2 ^ k := by
      norm_num [pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_w2,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_node2,
        pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_r2]
    unfold pom_diagonal_rate_refresh_holding_interval_pgf_hausdorff_completeMonotoneWitness
    linarith

end Omega.POM
