import Mathlib.Tactic
import Omega.Conclusion.CanonicalFixedpointFullshiftConjugacy

namespace Omega.Zeta

open Omega.Conclusion

/-- Agreement on the first `n` digits of two canonical streams. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_prefixAgree (D : CanonicalSliceData)
    (n : ℕ) (a b : CanonicalDigitStream D) : Prop :=
  ∀ t < n, a t = b t

/-- The first disagreement occurs at digit `n`. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_firstDifferenceAt
    (D : CanonicalSliceData) (n : ℕ) (a b : CanonicalDigitStream D) : Prop :=
  xi_time_part9g_holographic_prefix_isometry_on_line_prefixAgree D n a b ∧ a n ≠ b n

/-- Valuation statement: the two addresses agree modulo the `n`-prefix coset, but not modulo the
next one. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_valuationAt (D : CanonicalSliceData)
    (n : ℕ) (a b : CanonicalDigitStream D) : Prop :=
  canonicalPrefix D n a = canonicalPrefix D n b ∧
    canonicalPrefix D (n + 1) a ≠ canonicalPrefix D (n + 1) b

/-- The prefix ultrametric at disagreement depth `n`. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_prefixMetric (D : CanonicalSliceData)
    (n : ℕ) : ℚ :=
  ((D.M + 1 : ℚ)⁻¹) ^ n

/-- The transported `B`-adic metric on the address line. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_addressMetric (D : CanonicalSliceData)
    (n : ℕ) : ℚ :=
  ((D.M + 1 : ℚ)⁻¹) ^ n

/-- The address map of the canonical holographic model. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_address (D : CanonicalSliceData) :
    CanonicalDigitStream D → CanonicalFixedpointCode D :=
  canonicalDigitEncoder D

/-- Cylinder of streams with a fixed prefix. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_cylinder (D : CanonicalSliceData)
    (n : ℕ) (w : D.fixedPointsAtLayer n) : Set (CanonicalDigitStream D) :=
  {a | canonicalPrefix D n a = w}

/-- Coset of coded addresses with a fixed prefix. -/
def xi_time_part9g_holographic_prefix_isometry_on_line_coset (D : CanonicalSliceData) (n : ℕ)
    (w : D.fixedPointsAtLayer n) : Set (CanonicalFixedpointCode D) :=
  {c | canonicalPrefix D n c = w}

lemma xi_time_part9g_holographic_prefix_isometry_on_line_prefix_eq
    (D : CanonicalSliceData) {n : ℕ} {a b : CanonicalDigitStream D}
    (h :
      xi_time_part9g_holographic_prefix_isometry_on_line_prefixAgree D n a b) :
    canonicalPrefix D n a = canonicalPrefix D n b := by
  funext i
  exact h i i.2

lemma xi_time_part9g_holographic_prefix_isometry_on_line_prefix_ne
    (D : CanonicalSliceData) {n : ℕ} {a b : CanonicalDigitStream D}
    (h :
      xi_time_part9g_holographic_prefix_isometry_on_line_firstDifferenceAt D n a b) :
    canonicalPrefix D (n + 1) a ≠ canonicalPrefix D (n + 1) b := by
  intro hEq
  apply h.2
  have hDigit := congrFun hEq ⟨n, Nat.lt_succ_self n⟩
  simpa [canonicalPrefix] using hDigit

/-- Paper label: `thm:xi-time-part9g-holographic-prefix-isometry-on-line`. In the canonical
fixed-point model the first differing digit is exactly the first level where the two coded
addresses fall into different prefix cosets, the transported `B`-adic metric agrees with the
prefix metric, and cylinders are carried to the corresponding address cosets. -/
theorem paper_xi_time_part9g_holographic_prefix_isometry_on_line :
    ∀ (D : CanonicalSliceData) (n : ℕ) (a b : CanonicalDigitStream D),
      xi_time_part9g_holographic_prefix_isometry_on_line_firstDifferenceAt D n a b →
        xi_time_part9g_holographic_prefix_isometry_on_line_valuationAt D n a b ∧
          xi_time_part9g_holographic_prefix_isometry_on_line_addressMetric D n =
            xi_time_part9g_holographic_prefix_isometry_on_line_prefixMetric D n ∧
          ∀ w : D.fixedPointsAtLayer n,
            Set.image
                (xi_time_part9g_holographic_prefix_isometry_on_line_address D)
                (xi_time_part9g_holographic_prefix_isometry_on_line_cylinder D n w) =
              xi_time_part9g_holographic_prefix_isometry_on_line_coset D n w := by
  intro D n a b hdiff
  refine ⟨?_, rfl, ?_⟩
  · exact
      ⟨xi_time_part9g_holographic_prefix_isometry_on_line_prefix_eq D hdiff.1,
        xi_time_part9g_holographic_prefix_isometry_on_line_prefix_ne D hdiff⟩
  · intro w
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hc
      exact ⟨c, hc, rfl⟩

end Omega.Zeta
