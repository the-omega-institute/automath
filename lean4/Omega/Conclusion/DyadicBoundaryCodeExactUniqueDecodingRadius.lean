import Mathlib.Tactic
import Omega.SPG.DyadicBoundaryImageMinDistance

namespace Omega.Conclusion

/-- The radius up to which the dyadic boundary-image code is uniquely decodable. -/
def dyadicBoundaryCodeUniqueDecodingRadius (m n : ℕ) : ℕ :=
  (Omega.SPG.dyadicBoundaryImageMinDistance m n - 1) / 2

/-- The first radius where a midpoint witness can tie two codewords at distance `2n`. -/
def dyadicBoundaryCodeTieRadius (m n : ℕ) : ℕ :=
  Omega.SPG.dyadicBoundaryImageMinDistance m n / 2

set_option maxHeartbeats 400000 in
/-- The dyadic boundary-image code has exact unique decoding radius `n - 1`: the minimum distance
is `2n`, so uniqueness holds through radius `n - 1`, and the midpoint radius `n` is the sharp
boundary where ties first appear.
    thm:conclusion-dyadic-boundary-code-exact-unique-decoding-radius -/
theorem paper_conclusion_dyadic_boundary_code_exact_unique_decoding_radius
    (m n : ℕ) (hn : 1 ≤ n) :
    Omega.SPG.dyadicBoundaryImageMinDistance m n = 2 * n ∧
      dyadicBoundaryCodeUniqueDecodingRadius m n = n - 1 ∧
      dyadicBoundaryCodeTieRadius m n = n ∧
      dyadicBoundaryCodeUniqueDecodingRadius m n + 1 = dyadicBoundaryCodeTieRadius m n := by
  have hDist := Omega.SPG.paper_spg_dyadic_boundary_image_min_distance m n hn
  refine ⟨hDist, ?_, ?_, ?_⟩
  · simp [dyadicBoundaryCodeUniqueDecodingRadius, hDist]
    omega
  · simp [dyadicBoundaryCodeTieRadius, hDist]
  · simp [dyadicBoundaryCodeUniqueDecodingRadius, dyadicBoundaryCodeTieRadius, hDist]
    omega

end Omega.Conclusion
