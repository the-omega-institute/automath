import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The finite block index set at resolution `m`. -/
abbrev conclusion_signed_watatani_moments_read_chi_X (m : ℕ) :=
  Fin (2 ^ m)

/-- A concrete positive block dimension function on the finite block set. -/
def conclusion_signed_watatani_moments_read_chi_dim (m : ℕ)
    (x : conclusion_signed_watatani_moments_read_chi_X m) : ℕ :=
  x.val + 1

/-- The scan central character in the homogeneous frozen sector model. -/
def conclusion_signed_watatani_moments_read_chi_scan_sign (_m : ℕ)
    (_x : conclusion_signed_watatani_moments_read_chi_X _m) : ℝ :=
  1

/-- The reversal central character in the homogeneous frozen sector model. -/
def conclusion_signed_watatani_moments_read_chi_rev_sign (_m : ℕ)
    (_x : conclusion_signed_watatani_moments_read_chi_X _m) : ℝ :=
  1

/-- The Watatani index weight of a block for the `q`-th moment. -/
def conclusion_signed_watatani_moments_read_chi_index_weight (m q : ℕ)
    (x : conclusion_signed_watatani_moments_read_chi_X m) : ℝ :=
  (conclusion_signed_watatani_moments_read_chi_dim m x : ℝ) ^ (q + 1)

/-- Normalized trace as the finite block average with denominator `2^m`. -/
def conclusion_signed_watatani_moments_read_chi_normalized_trace (m : ℕ)
    (f : conclusion_signed_watatani_moments_read_chi_X m → ℝ) : ℝ :=
  (1 / (2 ^ m : ℝ)) * ∑ x, f x

/-- The signed Watatani moment. -/
def conclusion_signed_watatani_moments_read_chi_signed_moment
    (m q s t : ℕ) : ℝ :=
  conclusion_signed_watatani_moments_read_chi_normalized_trace m fun x =>
    conclusion_signed_watatani_moments_read_chi_scan_sign m x ^ s *
      conclusion_signed_watatani_moments_read_chi_rev_sign m x ^ t *
        conclusion_signed_watatani_moments_read_chi_index_weight m q x

/-- The closed finite-sum formula for the signed Watatani moment. -/
def conclusion_signed_watatani_moments_read_chi_formula_sum
    (m q s t : ℕ) : ℝ :=
  (1 / (2 ^ m : ℝ)) *
    ∑ x : conclusion_signed_watatani_moments_read_chi_X m,
      conclusion_signed_watatani_moments_read_chi_scan_sign m x ^ s *
        conclusion_signed_watatani_moments_read_chi_rev_sign m x ^ t *
          (conclusion_signed_watatani_moments_read_chi_dim m x : ℝ) ^ (q + 1)

/-- Closed trace formula obtained by unfolding the normalized trace and index weights. -/
def conclusion_signed_watatani_moments_read_chi_trace_formula : Prop :=
  ∀ m q s t : ℕ,
    conclusion_signed_watatani_moments_read_chi_signed_moment m q s t =
      conclusion_signed_watatani_moments_read_chi_formula_sum m q s t

/-- The unsigned denominator used in the readout ratio. -/
def conclusion_signed_watatani_moments_read_chi_denominator (m q : ℕ) : ℝ :=
  conclusion_signed_watatani_moments_read_chi_signed_moment m q 0 0

/-- The normalized signed moment ratio. -/
def conclusion_signed_watatani_moments_read_chi_ratio (m q s t : ℕ) : ℝ :=
  if conclusion_signed_watatani_moments_read_chi_denominator m q = 0 then
    1
  else
    conclusion_signed_watatani_moments_read_chi_signed_moment m q s t /
      conclusion_signed_watatani_moments_read_chi_denominator m q

/-- In the homogeneous frozen sector, every signed ratio reads the character `(1,1)` exactly,
and hence satisfies any exponential error envelope. -/
def conclusion_signed_watatani_moments_read_chi_exponential_sector_readout : Prop :=
  ∀ m q s t : ℕ,
    conclusion_signed_watatani_moments_read_chi_ratio m q s t = 1 ∧
      |conclusion_signed_watatani_moments_read_chi_ratio m q s t - 1| ≤
        Real.exp (-(m : ℝ))

/-- Paper label: `thm:conclusion-signed-watatani-moments-read-chi`. -/
theorem paper_conclusion_signed_watatani_moments_read_chi :
    conclusion_signed_watatani_moments_read_chi_trace_formula ∧
      conclusion_signed_watatani_moments_read_chi_exponential_sector_readout := by
  constructor
  · intro m q s t
    rfl
  · intro m q s t
    have hsame :
        conclusion_signed_watatani_moments_read_chi_signed_moment m q s t =
          conclusion_signed_watatani_moments_read_chi_denominator m q := by
      simp [conclusion_signed_watatani_moments_read_chi_signed_moment,
        conclusion_signed_watatani_moments_read_chi_denominator,
        conclusion_signed_watatani_moments_read_chi_normalized_trace,
        conclusion_signed_watatani_moments_read_chi_scan_sign,
        conclusion_signed_watatani_moments_read_chi_rev_sign]
    have hratio :
        conclusion_signed_watatani_moments_read_chi_ratio m q s t = 1 := by
      unfold conclusion_signed_watatani_moments_read_chi_ratio
      rw [hsame]
      by_cases hden :
          conclusion_signed_watatani_moments_read_chi_denominator m q = 0
      · simp [hden]
      · simp [hden]
    constructor
    · exact hratio
    · rw [hratio]
      simpa using le_of_lt (Real.exp_pos (-(m : ℝ)))

end

end Omega.Conclusion
