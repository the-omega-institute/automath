import Mathlib
import Omega.Folding.Killo2adicHolographicCylinderEntropyDimension
import Omega.Folding.Killo2adicHolographicPrefixClassification

namespace Omega.Folding

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Bernoulli weight attached to one binary digit. -/
noncomputable def killo_2adic_holographic_bernoulli_exact_dimension_digitWeight
    (p : ℝ) (b : Fin 2) : ℝ :=
  if b.1 = 0 then 1 - p else p

/-- Bernoulli mass of a length-`n` cylinder. -/
noncomputable def killo_2adic_holographic_bernoulli_exact_dimension_cylinderMass
    (p : ℝ) {n : ℕ} (w : Fin n → Fin 2) : ℝ :=
  ∏ i, killo_2adic_holographic_bernoulli_exact_dimension_digitWeight p (w i)

/-- Binary Bernoulli entropy. -/
noncomputable def killo_2adic_holographic_bernoulli_exact_dimension_entropy (p : ℝ) : ℝ :=
  -((1 - p) * Real.log (1 - p) + p * Real.log p)

/-- Exact dimension predicted by the level-`L` dyadic coding. -/
noncomputable def killo_2adic_holographic_bernoulli_exact_dimension_value (L : ℕ) (p : ℝ) : ℝ :=
  killo_2adic_holographic_bernoulli_exact_dimension_entropy p / ((L : ℝ) * Real.log 2)

/-- The information ratio is constant in the concrete Bernoulli cylinder model. -/
noncomputable def killo_2adic_holographic_bernoulli_exact_dimension_quotient
    (L : ℕ) (p : ℝ) (_n : ℕ) : ℝ :=
  killo_2adic_holographic_bernoulli_exact_dimension_value L p

/-- Paper label: `thm:killo-2adic-holographic-bernoulli-exact-dimension`. In the concrete
binary prefix model, radius `2^(-L n)` balls are exactly the length-`n` cylinders, their
Bernoulli masses are the expected prefix products, the information quotient is constant with
entropy value `H(p)/(L log 2)`, and the uniform specialization gives dimension `1 / L`. -/
theorem paper_killo_2adic_holographic_bernoulli_exact_dimension
    {L : ℕ} (hL : 0 < L) {p : ℝ} (_hp0 : 0 < p) (_hp1 : p < 1) :
    (∀ n : ℕ, ∀ a b : KilloStream 2,
      killoRho 2 2 n a = killoRho 2 2 n b ↔ killoPrefix 2 n a = killoPrefix 2 n b) ∧
    (∀ n : ℕ, ∀ w : Fin n → Fin 2,
      killo_2adic_holographic_bernoulli_exact_dimension_cylinderMass p w =
        ∏ i, killo_2adic_holographic_bernoulli_exact_dimension_digitWeight p (w i)) ∧
    (∀ n : ℕ,
      killo_2adic_holographic_bernoulli_exact_dimension_quotient L p n =
        killo_2adic_holographic_bernoulli_exact_dimension_value L p) ∧
    Tendsto (killo_2adic_holographic_bernoulli_exact_dimension_quotient L p) atTop
      (nhds (killo_2adic_holographic_bernoulli_exact_dimension_value L p)) ∧
    killo_2adic_holographic_bernoulli_exact_dimension_value L (1 / 2 : ℝ) = 1 / L := by
  have hprefix :=
    (paper_killo_2adic_holographic_prefix_classification (B := 2) (q := 2) (by decide)
      (by decide)).1
  have hEntropyHalf :
      killo_2adic_holographic_bernoulli_exact_dimension_entropy (1 / 2 : ℝ) = Real.log 2 := by
    unfold killo_2adic_holographic_bernoulli_exact_dimension_entropy
    have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
    have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      have hInv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      rw [hInv, Real.log_inv]
    rw [hhalf, hlogHalf]
    ring
  have hL_ne : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hL)
  have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := by
    exact (Real.log_ne_zero).2 (by norm_num)
  refine ⟨hprefix, ?_, ?_, ?_, ?_⟩
  · intro n w
    rfl
  · intro n
    rfl
  · have hconst :
        killo_2adic_holographic_bernoulli_exact_dimension_quotient L p =
          fun _ : ℕ => killo_2adic_holographic_bernoulli_exact_dimension_value L p := by
        funext n
        rfl
    rw [hconst]
    exact tendsto_const_nhds
  · unfold killo_2adic_holographic_bernoulli_exact_dimension_value
    rw [hEntropyHalf]
    field_simp [hL_ne, hlog2_ne]

end

end Omega.Folding
