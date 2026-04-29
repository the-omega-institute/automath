import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-endpoint-single-eigenpair-inverts-threshold-atlas`. -/
theorem paper_conclusion_endpoint_single_eigenpair_inverts_threshold_atlas {n : Nat}
    (t v w : Fin n → Real) (lam sigma : Real) (thresholdAtlasRecovered : Prop)
    (ht_inj : Function.Injective t) (hv_nonzero : ∃ x, v x ≠ 0)
    (hsigma : sigma = Finset.univ.sum v) (heig : ∀ x, (t x - lam) * v x = sigma)
    (hw : ∀ x, w x = (1 / (t x)^2) / (Finset.univ.sum fun u => 1 / (t u)^2))
    (hatlas : thresholdAtlasRecovered) :
    sigma ≠ 0 ∧
      (∀ x, v x ≠ 0 ∧ t x = lam + sigma / v x) ∧
        (∀ x,
          w x =
            (1 / (lam + sigma / v x)^2) /
              (Finset.univ.sum fun u => 1 / (lam + sigma / v u)^2)) ∧
          thresholdAtlasRecovered := by
  classical
  rcases hv_nonzero with ⟨x₀, hvx₀⟩
  have hsigma_ne : sigma ≠ 0 := by
    intro hsigma_zero
    have htx₀ : t x₀ = lam := by
      have hx := heig x₀
      rw [hsigma_zero] at hx
      exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hvx₀)
    have hv_zero_of_ne : ∀ y, y ≠ x₀ → v y = 0 := by
      intro y hy
      have hy_eig := heig y
      rw [hsigma_zero] at hy_eig
      rcases mul_eq_zero.mp hy_eig with hdiff | hvy
      · exfalso
        have hty : t y = lam := sub_eq_zero.mp hdiff
        have htyx₀ : t y = t x₀ := by rw [hty, htx₀]
        exact hy (ht_inj htyx₀)
      · exact hvy
    have hsum_eq : (∑ y, v y) = v x₀ := by
      exact Finset.sum_eq_single x₀ (fun y _ hy => hv_zero_of_ne y hy) (by simp)
    have hvx₀_zero : v x₀ = 0 := by
      have hsum_zero : (∑ y, v y) = 0 := by
        simpa [hsigma_zero] using hsigma.symm
      simpa [hsum_eq] using hsum_zero
    exact hvx₀ hvx₀_zero
  have hv_all : ∀ x, v x ≠ 0 := by
    intro x hvx
    have hx := heig x
    rw [hvx, mul_zero] at hx
    exact hsigma_ne hx.symm
  have ht_formula : ∀ x, v x ≠ 0 ∧ t x = lam + sigma / v x := by
    intro x
    refine ⟨hv_all x, ?_⟩
    have hvx := hv_all x
    have hdiff : t x - lam = sigma / v x := by
      calc
        t x - lam = ((t x - lam) * v x) / v x := by field_simp [hvx]
        _ = sigma / v x := by rw [heig x]
    linarith
  have hw_formula :
      ∀ x,
        w x =
          (1 / (lam + sigma / v x)^2) /
            (Finset.univ.sum fun u => 1 / (lam + sigma / v u)^2) := by
    have ht_values : ∀ x, t x = lam + sigma / v x := fun x => (ht_formula x).2
    intro x
    simpa [ht_values] using hw x
  exact ⟨hsigma_ne, ht_formula, hw_formula, hatlas⟩

end Omega.Conclusion
