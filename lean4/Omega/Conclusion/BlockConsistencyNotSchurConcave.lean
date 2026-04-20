import Mathlib.Tactic
import Omega.Conclusion.CapacityMajorizationSchurHardness

namespace Omega.Conclusion

/-- The block response obtained after collapsing a fine law to two block masses. -/
def blockResponse (δ : ℝ × ℝ) : List ℝ → ℝ
  | [w₀, w₁] => δ.1 * w₀ + δ.2 * w₁
  | _ => 0

/-- A concrete Schur-concavity predicate for block laws, phrased using the chapter's majorization
order. -/
def BlockSchurConcave (F : List ℝ → ℝ) : Prop :=
  ∀ d e : List ℝ, majorizes d e → F d ≤ F e

lemma majorizes_swap_two (a b : ℝ) : majorizes [a, b] [b, a] := by
  intro u
  simp [tailPositiveSum, positivePart, add_comm]

lemma eq_of_blockSchurConcave {F : List ℝ → ℝ} (hF : BlockSchurConcave F)
    {d e : List ℝ} (hde : majorizes d e) (hed : majorizes e d) : F d = F e := by
  exact le_antisymm (hF d e hde) (hF e d hed)

/-- A two-block consistency score can be rewritten through the collapsed block law, but the value
depends on which block receives the mass. The transposed block laws `[1, 0]` and `[0, 1]`
majorize each other, so any Schur-concave score would have to agree on them; the concrete block
response with `δ = (1, 0)` does not, hence block consistency is not Schur-concave.
    prop:conclusion-block-consistency-not-schur-concave -/
theorem paper_conclusion_block_consistency_not_schur_concave :
    let δ : ℝ × ℝ := (1, 0)
    let W : List ℝ := [1, 0]
    let Wswap : List ℝ := [0, 1]
    blockResponse δ W = 1 ∧
      blockResponse δ Wswap = 0 ∧
      majorizes W Wswap ∧
      majorizes Wswap W ∧
      ¬ BlockSchurConcave (blockResponse δ) := by
  refine ⟨by norm_num [blockResponse], by norm_num [blockResponse], majorizes_swap_two 1 0,
    majorizes_swap_two 0 1, ?_⟩
  intro hδ
  have hEq :
      blockResponse (1, 0) [1, 0] = blockResponse (1, 0) [0, 1] :=
    eq_of_blockSchurConcave hδ (majorizes_swap_two 1 0) (majorizes_swap_two 0 1)
  norm_num [blockResponse] at hEq

end Omega.Conclusion
