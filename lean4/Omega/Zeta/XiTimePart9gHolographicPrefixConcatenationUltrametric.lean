import Mathlib.Tactic
import Omega.Conclusion.CanonicalFixedpointFullshiftConjugacy
import Omega.Zeta.XiTimePart9gHolographicPrefixIsometryOnLine

namespace Omega.Zeta

open Omega.Conclusion

/-- Prefix a finite canonical block to an infinite canonical digit stream. -/
def xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend
    (D : CanonicalSliceData) (k : ℕ) (w : D.fixedPointsAtLayer k) (e : CanonicalDigitStream D) :
    CanonicalDigitStream D :=
  fun n =>
    if h : n < k then
      w ⟨n, h⟩
    else
      e (n - k)

lemma xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend_prefix
    (D : CanonicalSliceData) (k : ℕ) (w : D.fixedPointsAtLayer k) (e : CanonicalDigitStream D) :
    canonicalPrefix D k
        (xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend D k w e) =
      w := by
  funext i
  simp [canonicalPrefix, xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend, i.2]

/-- Paper label: `thm:xi-time-part9g-holographic-prefix-concatenation-ultrametric`. Prefixing a
canonical stream by a fixed length-`k` block preserves that prefix exactly, and it shifts the
first-difference depth by `k`. -/
theorem paper_xi_time_part9g_holographic_prefix_concatenation_ultrametric
    (D : CanonicalSliceData) :
    (∀ k (w : D.fixedPointsAtLayer k) (e : CanonicalDigitStream D),
      canonicalPrefix D k
          (xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend D k w e) = w) ∧
      (∀ k (w : D.fixedPointsAtLayer k) (n : ℕ) (e e' : CanonicalDigitStream D),
        xi_time_part9g_holographic_prefix_isometry_on_line_firstDifferenceAt D n e e' →
          xi_time_part9g_holographic_prefix_isometry_on_line_firstDifferenceAt D (k + n)
            (xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend D k w e)
            (xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend D k w e')) := by
  refine ⟨?_, ?_⟩
  · intro k w e
    exact
      xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend_prefix D k w e
  · intro k w n e e' hdiff
    refine ⟨?_, ?_⟩
    · intro t ht
      by_cases hk : t < k
      · simp [xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend, hk]
      · have htk : k ≤ t := Nat.le_of_not_gt hk
        have hsub : t - k < n := by
          omega
        simpa [xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend, hk] using
          hdiff.1 (t - k) hsub
    · have hk' : ¬ k + n < k := by
        omega
      simpa [xi_time_part9g_holographic_prefix_concatenation_ultrametric_prepend, hk',
        Nat.add_sub_cancel_left k n] using hdiff.2

end Omega.Zeta
