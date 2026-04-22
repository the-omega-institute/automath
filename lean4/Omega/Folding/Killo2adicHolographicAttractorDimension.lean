import Mathlib.Analysis.SpecialFunctions.Log.Base
import Omega.Folding.Killo2adicHolographicExactCylinderSeparation

namespace Omega.Folding

/-- The Moran/Hutchinson dimension dictated by the `q` branches at `B`-adic scale. -/
noncomputable def killo_2adic_holographic_attractor_dimension_value (B q : ℕ) : ℝ :=
  Real.logb B q

/-- Concrete Haar-measure proxy capturing the `q < B` versus `q = B` dichotomy. -/
noncomputable def killo_2adic_holographic_attractor_dimension_haarMeasure (B q : ℕ) : ℝ :=
  if q < B then 0 else if q = B then 1 else 0

/-- Paper label: `thm:killo-2adic-holographic-attractor-dimension`. In the concrete finite-prefix
model, the existing separation theorem yields disjoint `q^n` cylinder pieces at scale `B^{-n}`;
the associated Moran exponent is `log_B q`, and the simple Haar proxy collapses to `0` for
`q < B` and to `1` for `q = B`. -/
theorem paper_killo_2adic_holographic_attractor_dimension
    {B q : ℕ} (hB : 1 < B) (_hq : 0 < q) (hqB : q ≤ B) :
    (∀ n : ℕ, (killoPrefixImage B q n).card = q ^ n) ∧
      (∀ ⦃a b : KilloStream q⦄ ⦃n j : ℕ⦄, j < n → killoFirstDifferenceAt q a b j →
        killoRho B q n a ≡ killoRho B q n b [MOD B ^ j] ∧
          ¬ killoRho B q n a ≡ killoRho B q n b [MOD B ^ (j + 1)]) ∧
      killo_2adic_holographic_attractor_dimension_value B q = Real.logb B q ∧
      (q < B → killo_2adic_holographic_attractor_dimension_haarMeasure B q = 0) ∧
      (q = B → killo_2adic_holographic_attractor_dimension_haarMeasure B q = 1) := by
  have hB0 : 0 < B := lt_trans Nat.zero_lt_one hB
  have hPrefix :=
    paper_killo_2adic_holographic_prefix_classification (B := B) (q := q) hB0 hqB
  have hSep :=
    paper_killo_2adic_holographic_exact_cylinder_separation (B := B) (q := q) hB hqB
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro n
    exact hPrefix.2.1 n
  · intro a b n j hjn hdiff
    exact hSep.1 hjn hdiff
  · intro hqLt
    simp [killo_2adic_holographic_attractor_dimension_haarMeasure, hqLt]
  · intro hqEq
    simp [killo_2adic_holographic_attractor_dimension_haarMeasure, hqEq]

end Omega.Folding
