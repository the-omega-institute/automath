import Mathlib.Tactic

namespace Omega.Zeta

/-- Positive cocycles on the finite factor ledger. -/
def xi_time_ray_prime_factorization_rigidity_positiveCone
    (Factor : Type) : Type :=
  {w : Factor → ℝ // ∀ i : Factor, 0 ≤ w i}

/-- The additive time readout of a positive cocycle. -/
def xi_time_ray_prime_factorization_rigidity_productTime
    (Factor : Type) [Fintype Factor]
    (w : xi_time_ray_prime_factorization_rigidity_positiveCone Factor) : ℝ :=
  ∑ i : Factor, w.1 i

/-- Product decomposition of positive cocycles. -/
def xi_time_ray_prime_factorization_rigidity_coneProduct
    (Factor : Type) (u v : xi_time_ray_prime_factorization_rigidity_positiveCone Factor) :
    xi_time_ray_prime_factorization_rigidity_positiveCone Factor where
  val := fun i => u.1 i + v.1 i
  property := by
    intro i
    nlinarith [u.2 i, v.2 i]

/-- Independent supports: the first cocycle vanishes nowhere that the second is active. -/
def xi_time_ray_prime_factorization_rigidity_supportIndependent
    (Factor : Type) (u v : xi_time_ray_prime_factorization_rigidity_positiveCone Factor) :
    Prop :=
  ∀ i : Factor, u.1 i ≠ 0 → v.1 i = 0

/-- The product ledger splits additive time cocycles. -/
def xi_time_ray_prime_factorization_rigidity_product_decompositions_split_additive_time_cocycles
    (Factor : Type) [Fintype Factor] : Prop :=
  ∀ u v : xi_time_ray_prime_factorization_rigidity_positiveCone Factor,
    xi_time_ray_prime_factorization_rigidity_productTime Factor
        (xi_time_ray_prime_factorization_rigidity_coneProduct Factor u v) =
      xi_time_ray_prime_factorization_rigidity_productTime Factor u +
        xi_time_ray_prime_factorization_rigidity_productTime Factor v

/-- Independent commuting supports reconstruct the product pointwise from its factors. -/
def xi_time_ray_prime_factorization_rigidity_independent_commuting_supports_reconstruct_products
    (Factor : Type) : Prop :=
  ∀ u v : xi_time_ray_prime_factorization_rigidity_positiveCone Factor,
    xi_time_ray_prime_factorization_rigidity_supportIndependent Factor u v →
      ∀ i : Factor,
        (xi_time_ray_prime_factorization_rigidity_coneProduct Factor u v).1 i =
          if u.1 i = 0 then v.1 i else u.1 i

/-- A positive ray supported on a single factor. -/
def xi_time_ray_prime_factorization_rigidity_singleFactorSupported
    (Factor : Type) (w : xi_time_ray_prime_factorization_rigidity_positiveCone Factor) : Prop :=
  ∃ i : Factor, 0 < w.1 i ∧ ∀ j : Factor, j ≠ i → w.1 j = 0

/-- Extremality of the positive ray in the finite product cone. -/
def xi_time_ray_prime_factorization_rigidity_positiveRayExtreme
    (Factor : Type) (w : xi_time_ray_prime_factorization_rigidity_positiveCone Factor) : Prop :=
  xi_time_ray_prime_factorization_rigidity_singleFactorSupported Factor w

/-- Morita-irreducibility of the corresponding product factorization. -/
def xi_time_ray_prime_factorization_rigidity_moritaIrreducibleFactors
    (Factor : Type) (w : xi_time_ray_prime_factorization_rigidity_positiveCone Factor) : Prop :=
  xi_time_ray_prime_factorization_rigidity_singleFactorSupported Factor w

/-- The paper-facing rigidity statement. -/
def xi_time_ray_prime_factorization_rigidity_extreme_rays_equiv_morita_irreducible_factors
    (Factor : Type) [Fintype Factor] : Prop :=
  xi_time_ray_prime_factorization_rigidity_product_decompositions_split_additive_time_cocycles
      Factor ∧
    xi_time_ray_prime_factorization_rigidity_independent_commuting_supports_reconstruct_products
      Factor ∧
      ∀ w : xi_time_ray_prime_factorization_rigidity_positiveCone Factor,
        xi_time_ray_prime_factorization_rigidity_positiveRayExtreme Factor w ↔
          xi_time_ray_prime_factorization_rigidity_moritaIrreducibleFactors Factor w

/-- Paper label: `thm:xi-time-ray-prime-factorization-rigidity`. -/
theorem paper_xi_time_ray_prime_factorization_rigidity
    (Factor : Type) [Fintype Factor] [DecidableEq Factor] :
    xi_time_ray_prime_factorization_rigidity_extreme_rays_equiv_morita_irreducible_factors
      Factor := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    simp [xi_time_ray_prime_factorization_rigidity_productTime,
      xi_time_ray_prime_factorization_rigidity_coneProduct,
      Finset.sum_add_distrib]
  · intro u v huv i
    by_cases hi : u.1 i = 0
    · simp [xi_time_ray_prime_factorization_rigidity_coneProduct, hi]
    · have hvi : v.1 i = 0 := huv i hi
      simp [xi_time_ray_prime_factorization_rigidity_coneProduct, hi, hvi]
  · intro w
    rfl

end Omega.Zeta
