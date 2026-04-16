import Mathlib.Tactic

namespace Omega.POM

/-- Odd zero segments contribute one antipode phase and even zero segments contribute two. -/
def zeroSegmentPhaseChoices : List ℕ → ℕ
  | [] => 1
  | L :: segments => (if Even L then 2 else 1) * zeroSegmentPhaseChoices segments

/-- Count of even zero segments in a maximal zero-run decomposition. -/
def evenZeroSegmentCount (segments : List ℕ) : ℕ :=
  match segments with
  | [] => 0
  | L :: rest => (if Even L then 1 else 0) + evenZeroSegmentCount rest

/-- The segmentwise phase product collapses to a power of two indexed by the even segments. -/
theorem zeroSegmentPhaseChoices_eq_pow_evenZeroSegmentCount :
    ∀ segments : List ℕ,
      zeroSegmentPhaseChoices segments = 2 ^ evenZeroSegmentCount segments
  | [] => by simp [zeroSegmentPhaseChoices, evenZeroSegmentCount]
  | L :: segments => by
      by_cases hEven : Even L
      · calc
          zeroSegmentPhaseChoices (L :: segments)
              = 2 * zeroSegmentPhaseChoices segments := by
                  simp [zeroSegmentPhaseChoices, hEven]
          _ = 2 * 2 ^ evenZeroSegmentCount segments := by
                rw [zeroSegmentPhaseChoices_eq_pow_evenZeroSegmentCount segments]
          _ = 2 ^ (evenZeroSegmentCount segments + 1) := by
                rw [pow_succ, Nat.mul_comm]
          _ = 2 ^ evenZeroSegmentCount (L :: segments) := by
                simp [evenZeroSegmentCount, hEven, Nat.add_comm]
      · calc
          zeroSegmentPhaseChoices (L :: segments)
              = zeroSegmentPhaseChoices segments := by
                  simp [zeroSegmentPhaseChoices, hEven]
          _ = 2 ^ evenZeroSegmentCount segments := by
                rw [zeroSegmentPhaseChoices_eq_pow_evenZeroSegmentCount segments]
          _ = 2 ^ evenZeroSegmentCount (L :: segments) := by
                simp [evenZeroSegmentCount, hEven]

set_option maxHeartbeats 400000 in
/-- Publication-facing phase-count formula for Fibonacci-cube antipodes:
the total number of antipode choices is `2 ^ r_even`, where `r_even` counts the even zero
segments in the maximal zero-run decomposition.
    prop:pom-fibcube-antipode-count -/
theorem paper_pom_fibcube_antipode_count (zeroSegments : List ℕ) :
    zeroSegmentPhaseChoices zeroSegments = 2 ^ evenZeroSegmentCount zeroSegments :=
  zeroSegmentPhaseChoices_eq_pow_evenZeroSegmentCount zeroSegments

end Omega.POM
