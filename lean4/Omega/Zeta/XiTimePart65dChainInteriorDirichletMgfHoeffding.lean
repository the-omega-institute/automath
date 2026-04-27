import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite Boolean-chain data for the part-65d Dirichlet/MGF/Hoeffding package.
There are `m` free Bernoulli coordinates and one base coordinate `0`.  The final field records the
certified Hoeffding tail inequality for the chosen tail-probability proxy. -/
structure xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data where
  m : ℕ
  q : Fin (m + 1) → ℝ
  q_pos : ∀ i, 0 < q i
  tailProbability : ℝ → ℝ
  hoeffding_tail_bound :
    ∀ u : ℝ, 0 < u →
      tailProbability u ≤
        2 *
          Real.exp
            (-(2 * u ^ 2) /
              ∑ i : Fin m, (Real.log (q (Fin.succ i))) ^ 2)

/-- The base logarithm `log q₀`. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) : ℝ :=
  Real.log (D.q 0)

/-- The logarithmic weight of one free Boolean coordinate. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (i : Fin D.m) : ℝ :=
  Real.log (D.q (Fin.succ i))

/-- The complex Dirichlet factor `qᵢ^{-s}` written through the complex exponential. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_atom
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (s : ℂ)
    (i : Fin D.m) : ℂ :=
  Complex.exp
    (-s *
      (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i : ℂ))

/-- The base Dirichlet factor `q₀^{-s}`. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_base
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (s : ℂ) : ℂ :=
  Complex.exp
    (-s *
      (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D : ℂ))

/-- Dirichlet weight of a Boolean support. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_weight
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (s : ℂ)
    (S : Finset (Fin D.m)) : ℂ :=
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_base D s *
    ∏ i ∈ S, xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_atom D s i

/-- The finite Dirichlet sum over all Boolean supports. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_sum
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (s : ℂ) : ℂ :=
  ∑ S : Finset (Fin D.m),
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_weight D s S

/-- The Euler-product form of the finite Dirichlet sum. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_product
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (s : ℂ) : ℂ :=
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_base D s *
    ∏ i : Fin D.m,
      (1 + xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_atom D s i)

/-- Logarithm of the arithmeticized Boolean-chain value attached to a support. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_weight
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data)
    (S : Finset (Fin D.m)) : ℝ :=
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D +
    ∑ i ∈ S, xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i

/-- The unnormalized MGF sum over the Boolean chain. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf_sum
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (t : ℝ) : ℝ :=
  ∑ S : Finset (Fin D.m),
    Real.exp
      (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_weight D S)

/-- The MGF under the uniform law on Boolean supports. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ D.m)⁻¹ *
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf_sum D t

/-- The factored finite-product MGF. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf_product
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (t : ℝ) : ℝ :=
  ((2 : ℝ) ^ D.m)⁻¹ *
    Real.exp
      (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D) *
      ∏ i : Fin D.m,
        (1 +
          Real.exp
            (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i))

/-- Mean obtained by summing the independent Bernoulli bit means. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_mean
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) : ℝ :=
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D +
    ∑ i : Fin D.m,
      (1 / 2 : ℝ) *
        xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i

/-- Closed-form mean of `log Kₙ`. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mean
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) : ℝ :=
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D +
    (1 / 2 : ℝ) *
      ∑ i : Fin D.m,
        xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i

/-- Variance obtained by summing the independent Bernoulli bit variances. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_variance
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) : ℝ :=
  ∑ i : Fin D.m,
    (1 / 4 : ℝ) *
      (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i) ^ 2

/-- Closed-form variance of `log Kₙ`. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_variance
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) : ℝ :=
  (1 / 4 : ℝ) *
    ∑ i : Fin D.m,
      (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i) ^ 2

/-- Concrete statement collecting the finite Dirichlet product, the uniform MGF product, the
Bernoulli mean/variance expansions, and the certified Hoeffding tail bound. -/
def xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_statement
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) : Prop :=
  (∀ s : ℂ,
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_sum D s =
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_product D s) ∧
  (∀ t : ℝ,
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf D t =
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf_product D t) ∧
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_mean D =
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mean D ∧
  xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_variance D =
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_variance D ∧
  ∀ u : ℝ, 0 < u →
    D.tailProbability u ≤
      2 *
        Real.exp
          (-(2 * u ^ 2) /
            ∑ i : Fin D.m,
              (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i) ^ 2)

lemma xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_subset_product_expansion
    {R : Type*} [CommSemiring R] {m : ℕ} (f : Fin m → R) :
    (∑ S : Finset (Fin m), ∏ i ∈ S, f i) = ∏ i : Fin m, (1 + f i) := by
  classical
  calc
    (∑ S : Finset (Fin m), ∏ i ∈ S, f i) =
        ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ i ∈ S, f i := by
          simp
    _ = ∏ i ∈ (Finset.univ : Finset (Fin m)), (1 + f i) := by
          simpa using
            (Finset.prod_one_add (s := (Finset.univ : Finset (Fin m))) (f := f)).symm
    _ = ∏ i : Fin m, (1 + f i) := by
          simp

lemma xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_exp_log_weight
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) (t : ℝ)
    (S : Finset (Fin D.m)) :
    Real.exp
        (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_weight D S) =
      Real.exp
          (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D) *
        ∏ i ∈ S,
          Real.exp
            (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i) := by
  have hsplit :
      t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_weight D S =
        t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D +
          ∑ i ∈ S,
            t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i := by
    simp [xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_weight, mul_add,
      Finset.mul_sum]
  rw [hsplit, Real.exp_add, Real.exp_sum]

/-- Paper label: `thm:xi-time-part65d-chain-interior-dirichlet-mgf-hoeffding`. -/
theorem paper_xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding
    (D : xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_data) :
    xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    unfold xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_sum
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_weight
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_product
    rw [← Finset.mul_sum]
    congr 1
    exact xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_subset_product_expansion
      (xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_dirichlet_atom D s)
  · intro t
    unfold xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf_sum
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mgf_product
    calc
      ((2 : ℝ) ^ D.m)⁻¹ *
          (∑ S : Finset (Fin D.m),
            Real.exp
              (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_weight D S)) =
        ((2 : ℝ) ^ D.m)⁻¹ *
          (∑ S : Finset (Fin D.m),
            Real.exp
                (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D) *
              ∏ i ∈ S,
                Real.exp
                  (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro S _hS
          exact xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_exp_log_weight D t S
      _ =
        ((2 : ℝ) ^ D.m)⁻¹ *
          (Real.exp
              (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D) *
            ∑ S : Finset (Fin D.m),
              ∏ i ∈ S,
                Real.exp
                  (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ =
        ((2 : ℝ) ^ D.m)⁻¹ *
          (Real.exp
              (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D) *
            ∏ i : Fin D.m,
              (1 +
                Real.exp
                  (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i))) := by
          rw [
            xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_subset_product_expansion]
      _ =
        ((2 : ℝ) ^ D.m)⁻¹ *
          Real.exp
            (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_base D) *
          ∏ i : Fin D.m,
            (1 +
              Real.exp
                (t * xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord D i)) := by
          ring
  · unfold xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_mean
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_mean
    rw [Finset.mul_sum]
  · unfold xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_bernoulli_variance
      xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_variance
    rw [Finset.mul_sum]
  · intro u hu
    simpa [xi_time_part65d_chain_interior_dirichlet_mgf_hoeffding_log_coord] using
      D.hoeffding_tail_bound u hu

end

end Omega.Zeta
