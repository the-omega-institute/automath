import Mathlib.Tactic
import Omega.Zeta.XiTimePart9gHolographicPrefixIsometryOnLine

namespace Omega.Zeta

open Omega.Conclusion

/-- The length-`k` block `r` viewed as a periodic canonical digit stream. For `k = 0` this is the
constant-zero stream, which is harmless because `D.fixedPointsAtLayer 0` is a singleton. -/
def xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream
    {D : CanonicalSliceData} {k : Nat} (r : D.fixedPointsAtLayer k) : CanonicalDigitStream D :=
  fun t =>
    if hk : 0 < k then
      r ⟨t % k, Nat.mod_lt t hk⟩
    else
      0

/-- Paper-facing stratification statement for canonical periodic fixed-point blocks. -/
def xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_statement
    (D : Omega.Conclusion.CanonicalSliceData) (k : Nat) : Prop :=
  (∀ r : D.fixedPointsAtLayer k, ∃! x, D.IsFixedPoint r k x) ∧
    Function.Injective
      (fun r : D.fixedPointsAtLayer k =>
        canonicalDigitEncoder D
          (xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream r)) ∧
    Fintype.card (D.fixedPointsAtLayer k) = (D.M + 1) ^ k ∧
    ∀ n, n ≤ k →
      ∀ r s : D.fixedPointsAtLayer k,
        (canonicalPrefix D n
            (xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream r) =
          canonicalPrefix D n
            (xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream s) ↔
          canonicalDigitEncoder D
              (xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream r) ∈
            xi_time_part9g_holographic_prefix_isometry_on_line_coset D n
              (canonicalPrefix D n
                (xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream
                  s)))

/-- Paper label: `thm:xi-time-part9gb-canonical-fixedpoint-count-prefix-stratification`. Every
canonical length-`k` block determines a unique fixed point, there are exactly `(M + 1)^k` such
blocks, and the `n`-prefix stratum is exactly the corresponding `B^n`-coset. -/
theorem paper_xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification
    (D : Omega.Conclusion.CanonicalSliceData) (k : Nat) :
    xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_statement D k := by
  classical
  refine ⟨?_, ?_, (paper_conclusion_canonical_slice_exact_fixedpoint_count D k).2, ?_⟩
  · intro r
    exact (paper_conclusion_canonical_slice_exact_fixedpoint_count D k).1 r (by
      simp [CanonicalSliceData.layer])
  · intro r s hcode
    by_cases hk : 0 < k
    · funext i
      have hdigit := congrFun hcode i.1
      simpa [canonicalDigitEncoder,
        xi_time_part9gb_canonical_fixedpoint_count_prefix_stratification_periodic_stream, hk,
        Nat.mod_eq_of_lt i.2] using hdigit
    · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      subst hk0
      funext i
      exact Fin.elim0 i
  · intro n hn r s
    constructor <;> intro h
    · simpa [xi_time_part9g_holographic_prefix_isometry_on_line_coset] using h
    · simpa [xi_time_part9g_holographic_prefix_isometry_on_line_coset] using h

end Omega.Zeta
