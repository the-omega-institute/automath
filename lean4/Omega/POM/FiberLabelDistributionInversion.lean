import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-fiber-label-distribution-inversion`. -/
theorem paper_pom_fiber_label_distribution_inversion {X G Χ : Type*} [Fintype G]
    [DecidableEq G] [Fintype Χ] (p : X → G → ℚ) (χ invχ : Χ → G → ℚ)
    (hcard : (Fintype.card Χ : ℚ) ≠ 0)
    (horth : ∀ g h : G,
      (∑ c : Χ, χ c h * invχ c g) =
        if h = g then (Fintype.card Χ : ℚ) else 0) :
    (let μ : X → Χ → ℚ := fun x c => ∑ h : G, p x h * χ c h
     ∀ x g, p x g = ((Fintype.card Χ : ℚ)⁻¹) * ∑ c : Χ, μ x c * invχ c g) := by
  dsimp
  intro x g
  symm
  calc
    ((Fintype.card Χ : ℚ)⁻¹) *
        (∑ c : Χ, (∑ h : G, p x h * χ c h) * invχ c g)
        =
      ((Fintype.card Χ : ℚ)⁻¹) *
        (∑ h : G, p x h * (∑ c : Χ, χ c h * invχ c g)) := by
        congr 1
        calc
          (∑ c : Χ, (∑ h : G, p x h * χ c h) * invχ c g)
              = ∑ c : Χ, ∑ h : G, (p x h * χ c h) * invχ c g := by
              simp [Finset.sum_mul]
          _ = ∑ h : G, ∑ c : Χ, (p x h * χ c h) * invχ c g := by
              rw [Finset.sum_comm]
          _ = ∑ h : G, p x h * (∑ c : Χ, χ c h * invχ c g) := by
              refine Finset.sum_congr rfl ?_
              intro h _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro c _
              ring
    _ =
      ((Fintype.card Χ : ℚ)⁻¹) *
        (∑ h : G, p x h * (if h = g then (Fintype.card Χ : ℚ) else 0)) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [horth g h]
    _ = ((Fintype.card Χ : ℚ)⁻¹) * (p x g * (Fintype.card Χ : ℚ)) := by
        congr 1
        rw [Finset.sum_eq_single g]
        · simp
        · intro h _ hhg
          simp [hhg]
        · intro hg
          exact False.elim (hg (Finset.mem_univ g))
    _ = p x g := by
        field_simp [hcard]

end Omega.POM
