import Mathlib.Tactic
import Omega.SPG.BoundaryGodelFiniteMomentCompleteness
import Omega.SPG.LinearMomentHolographyMinimalDimension

/-!
# Single-integer vs linear moment holography gap seed values

Power-of-two cardinalities, logarithm values, and gap inequalities.
-/

namespace Omega.SPG

/-- Single-integer vs linear moment holography gap seeds.
    thm:spg-single-integer-vs-linear-moment-holography-gap -/
theorem paper_spg_single_integer_vs_linear_moment_gap_seeds :
    (1 < 2 ^ (1 * 1) ∧ 1 < 2 ^ (2 * 1) ∧ 1 < 2 ^ (1 * 2)) ∧
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8 ∧ 2 ^ 4 = 16) ∧
    (2 ^ (2 * 3) = 64) ∧
    (Nat.log 2 4 = 2 ∧ Nat.log 2 8 = 3 ∧ Nat.log 2 16 = 4) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩,
         ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
         by norm_num,
         ⟨by native_decide, by native_decide, by native_decide⟩⟩

/-- Linear moment holography minimal dimension seeds.
    thm:spg-linear-moment-holography-minimal-dimension -/
theorem paper_spg_linear_moment_holography_minimal_dim_seeds :
    (2 ^ (1 * 1) = 2 ∧ 2 ^ (1 * 2) = 4 ∧ 2 ^ (2 * 2) = 16) ∧
    (∀ N L : Nat, L < N → 0 < N - L) ∧
    (2 ^ (2 * 1) = 4 ∧ 2 ^ (2 * 2) = 16 ∧ 2 ^ (2 * 3) = 64) ∧
    (2 ^ 3 = 8 ∧ 2 ^ 6 = 64 ∧ 8 < 64) := by
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, fun _ _ h => by omega,
         ⟨by norm_num, by norm_num, by norm_num⟩,
         ⟨by norm_num, by norm_num, by omega⟩⟩

/-- Paper-facing wrapper: a single natural-number readout already injects the finite dyadic state
    space, while any injective linear moment readout still obeys the `2^(m*n)` lower bound from
    `paper_spg_linear_moment_holography_minimal_dim`.
    thm:spg-single-integer-vs-linear-moment-holography-gap -/
theorem paper_spg_single_integer_vs_linear_moment_holography_gap
    (m n L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    Function.Injective (fun x : Fin (2 ^ (m * n)) => x.1) ∧
    2 ^ (m * n) ≤ L := by
  refine ⟨?_, (paper_spg_linear_moment_holography_minimal_dim m n L f hf).1⟩
  exact paper_spg_boundary_godel_finite_moment_completeness
    (encode := fun x : Fin (2 ^ (m * n)) => x.1)
    (momentBox := dyadicMomentBox (m := m) (n := n))
    (hReadout := by
      intro u v hEq
      exact Fin.ext hEq)
    paper_spg_dyadic_finite_moment_completeness

end Omega.SPG
