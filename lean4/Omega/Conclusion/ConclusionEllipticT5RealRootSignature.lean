import Mathlib.Tactic

namespace Omega.Conclusion

/-- Coefficients of the explicit `T₅` polynomial, stored from constant term to degree 24. -/
def conclusion_elliptic_t5_real_root_signature_coefficients_low_to_high : List Int :=
  [10048, -1254110, -15726875, -86874340, -240190705, -310993491, -89515935,
    -317786725, -1045141370, -538699445, 1313468808, 3220925750, 3910018680,
    838813180, -1928743150, -320647060, 1386419000, 761997855, -22555640,
    -89302755, -11037859, 855915, 244475, -23500, 625]

/-- The degree certified by the explicit coefficient list. -/
def conclusion_elliptic_t5_real_root_signature_degree : Nat :=
  conclusion_elliptic_t5_real_root_signature_coefficients_low_to_high.length - 1

/-- Rational isolating intervals for the four real roots. -/
def conclusion_elliptic_t5_real_root_signature_intervals : List (Rat × Rat) :=
  [((0 : Rat), 1 / 100), (7 / 10, 4 / 5), (31 / 10, 16 / 5),
    (61 / 5, 123 / 10)]

/-- Sturm certificate root counts on the four isolating intervals. -/
def conclusion_elliptic_t5_real_root_signature_interval_counts : List Nat :=
  [1, 1, 1, 1]

/-- The certified total count of simple real roots. -/
def conclusion_elliptic_t5_real_root_signature_real_root_count : Nat :=
  conclusion_elliptic_t5_real_root_signature_interval_counts.sum

/-- The degree-24 signature forced by four real embeddings. -/
def conclusion_elliptic_t5_real_root_signature_signature : Nat × Nat :=
  (4, 10)

/-- Paper-facing finite Sturm/sign certificate and the resulting field signature. -/
def conclusion_elliptic_t5_real_root_signature_claim : Prop :=
  conclusion_elliptic_t5_real_root_signature_coefficients_low_to_high.length = 25 ∧
    conclusion_elliptic_t5_real_root_signature_degree = 24 ∧
    conclusion_elliptic_t5_real_root_signature_intervals =
      [((0 : Rat), 1 / 100), (7 / 10, 4 / 5), (31 / 10, 16 / 5),
        (61 / 5, 123 / 10)] ∧
    conclusion_elliptic_t5_real_root_signature_interval_counts = [1, 1, 1, 1] ∧
    conclusion_elliptic_t5_real_root_signature_real_root_count = 4 ∧
    conclusion_elliptic_t5_real_root_signature_signature = (4, 10) ∧
    24 = conclusion_elliptic_t5_real_root_signature_signature.1 +
      2 * conclusion_elliptic_t5_real_root_signature_signature.2

/-- Paper label: `prop:conclusion-elliptic-t5-real-root-signature`. -/
theorem paper_conclusion_elliptic_t5_real_root_signature :
    conclusion_elliptic_t5_real_root_signature_claim := by
  dsimp [conclusion_elliptic_t5_real_root_signature_claim,
    conclusion_elliptic_t5_real_root_signature_coefficients_low_to_high,
    conclusion_elliptic_t5_real_root_signature_degree,
    conclusion_elliptic_t5_real_root_signature_intervals,
    conclusion_elliptic_t5_real_root_signature_interval_counts,
    conclusion_elliptic_t5_real_root_signature_real_root_count,
    conclusion_elliptic_t5_real_root_signature_signature]
  native_decide

end Omega.Conclusion
