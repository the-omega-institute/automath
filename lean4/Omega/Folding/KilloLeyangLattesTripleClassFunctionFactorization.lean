import Omega.Folding.GaugeAnomalyP10LeyangClassFunctionTensorIndependence

namespace Omega.Folding

open scoped BigOperators

/-- Paper label: `thm:killo-leyang-lattes-triple-class-function-factorization`. Expanding the
triple sum over the product type and then pulling out the two constant factors gives the
expected tensor factorization. -/
theorem paper_killo_leyang_lattes_triple_class_function_factorization
    (f : Equiv.Perm (Fin 10) → ℂ) (g : Equiv.Perm (Fin 3) → ℂ)
    (h : Equiv.Perm (Fin 4) × Fin 2 → ℂ) :
    (∑ x : Equiv.Perm (Fin 10) × Equiv.Perm (Fin 3) × (Equiv.Perm (Fin 4) × Fin 2),
        f x.1 * g x.2.1 * h x.2.2) =
      (∑ σ : Equiv.Perm (Fin 10), f σ) * (∑ τ : Equiv.Perm (Fin 3), g τ) *
        (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ) := by
  calc
    (∑ x : Equiv.Perm (Fin 10) × Equiv.Perm (Fin 3) × (Equiv.Perm (Fin 4) × Fin 2),
        f x.1 * g x.2.1 * h x.2.2) =
      ∑ σ : Equiv.Perm (Fin 10),
        ∑ y : Equiv.Perm (Fin 3) × (Equiv.Perm (Fin 4) × Fin 2), f σ * g y.1 * h y.2 := by
          rw [Fintype.sum_prod_type]
    _ =
      ∑ σ : Equiv.Perm (Fin 10), ∑ τ : Equiv.Perm (Fin 3), ∑ ξ : Equiv.Perm (Fin 4) × Fin 2,
        f σ * g τ * h ξ := by
          simp [Fintype.sum_prod_type]
    _ =
      ∑ σ : Equiv.Perm (Fin 10), ∑ τ : Equiv.Perm (Fin 3),
        (f σ * g τ) * (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ) := by
          simp [Finset.mul_sum, mul_assoc]
    _ = ∑ σ : Equiv.Perm (Fin 10), ∑ τ : Equiv.Perm (Fin 3),
        f σ * (g τ * (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ)) := by
          simp [mul_assoc]
    _ = ∑ σ : Equiv.Perm (Fin 10), f σ * (∑ τ : Equiv.Perm (Fin 3), g τ *
        (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ)) := by
          simp [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin 10), f σ * ((∑ τ : Equiv.Perm (Fin 3), g τ) *
        (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ)) := by
          rw [Finset.sum_mul]
    _ = (∑ σ : Equiv.Perm (Fin 10), f σ) * ((∑ τ : Equiv.Perm (Fin 3), g τ) *
        (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ)) := by
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Equiv.Perm (Fin 10))))
              (f := f)
              ((∑ τ : Equiv.Perm (Fin 3), g τ) *
                (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ))).symm
    _ = (∑ σ : Equiv.Perm (Fin 10), f σ) * (∑ τ : Equiv.Perm (Fin 3), g τ) *
        (∑ ξ : Equiv.Perm (Fin 4) × Fin 2, h ξ) := by
          ring

end Omega.Folding
