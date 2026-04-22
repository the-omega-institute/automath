import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-riccati-double-cayley-exact-isomorphism`. -/
theorem paper_conclusion_riccati_double_cayley_exact_isomorphism (t η q ρ : ℝ) (ht : 0 < t)
    (hη : Real.sinh η = Real.sqrt t / 2) (hq : q = Real.exp (-2 * η))
    (hρ : ρ = Real.tanh (η / 2)) :
    q = ((1 - ρ) / (1 + ρ)) ^ 2 ∧ t = (1 - q) ^ 2 / q := by
  have hρmem : ρ ∈ Set.Ioo (-1) 1 := by
    rw [hρ]
    exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have hhalf : Real.artanh ρ = η / 2 := by
    rw [hρ, Real.artanh_tanh]
  have hexp_half : Real.exp (η / 2) = Real.sqrt ((1 + ρ) / (1 - ρ)) := by
    calc
      Real.exp (η / 2) = Real.exp (Real.artanh ρ) := by rw [hhalf]
      _ = Real.sqrt ((1 + ρ) / (1 - ρ)) := Real.exp_artanh hρmem
  have hratio_pos : 0 ≤ (1 + ρ) / (1 - ρ) := by
    exact div_nonneg (by linarith [hρmem.1]) (by linarith [hρmem.2])
  have hexp_eta : Real.exp η = (1 + ρ) / (1 - ρ) := by
    have hsq : (Real.exp (η / 2)) ^ 2 = (1 + ρ) / (1 - ρ) := by
      have hsq' := congrArg (fun x : ℝ => x ^ 2) hexp_half
      simpa [Real.sq_sqrt hratio_pos] using hsq'
    have hexp_mul : Real.exp (η / 2) * Real.exp (η / 2) = Real.exp η := by
      calc
        Real.exp (η / 2) * Real.exp (η / 2) = Real.exp ((η / 2) + (η / 2)) := by
          rw [← Real.exp_add]
        _ = Real.exp η := by ring_nf
    calc
      Real.exp η = (Real.exp (η / 2)) ^ 2 := by simpa [sq] using hexp_mul.symm
      _ = (1 + ρ) / (1 - ρ) := hsq
  have hratio : (1 - ρ) / (1 + ρ) = Real.exp (-η) := by
    have h1 : 1 - ρ ≠ 0 := by linarith [hρmem.2]
    have h2 : 1 + ρ ≠ 0 := by linarith [hρmem.1]
    calc
      (1 - ρ) / (1 + ρ) = ((1 + ρ) / (1 - ρ))⁻¹ := by
        field_simp [h1, h2]
      _ = (Real.exp η)⁻¹ := by rw [hexp_eta]
      _ = Real.exp (-η) := by rw [Real.exp_neg]
  have hq_exp : q = (Real.exp (-η)) ^ 2 := by
    calc
      q = Real.exp (-2 * η) := hq
      _ = Real.exp ((-η) + (-η)) := by congr 1; ring
      _ = Real.exp (-η) * Real.exp (-η) := by rw [Real.exp_add]
      _ = (Real.exp (-η)) ^ 2 := by rw [sq]
  have hq_formula : q = ((1 - ρ) / (1 + ρ)) ^ 2 := by
    rw [hq_exp, hratio]
  have hsqrt : 2 * Real.sinh η = Real.sqrt t := by
    nlinarith [hη]
  have ht_exp : t = (Real.exp η - Real.exp (-η)) ^ 2 := by
    have hsq : (2 * Real.sinh η) ^ 2 = t := by
      rw [hsqrt, Real.sq_sqrt (le_of_lt ht)]
    calc
      t = (2 * ((Real.exp η - Real.exp (-η)) / 2)) ^ 2 := by simpa [Real.sinh_eq] using hsq.symm
      _ = (Real.exp η - Real.exp (-η)) ^ 2 := by ring_nf
  have hexp_inv : Real.exp η = (Real.exp (-η))⁻¹ := by
    simpa using (Real.exp_neg (-η))
  have hq_pos : 0 < q := by
    rw [hq]
    positivity
  have ht_formula : t = (1 - q) ^ 2 / q := by
    set x : ℝ := Real.exp (-η)
    have hx_pos : 0 < x := by
      dsimp [x]
      positivity
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hq_x : q = x ^ 2 := by
      simpa [x] using hq_exp
    calc
      t = ((Real.exp (-η))⁻¹ - Real.exp (-η)) ^ 2 := by rw [ht_exp, hexp_inv]
      _ = (x⁻¹ - x) ^ 2 := by simp [x]
      _ = (1 - x ^ 2) ^ 2 / (x ^ 2) := by
        field_simp [hx_ne]
      _ = (1 - q) ^ 2 / q := by rw [hq_x]
  exact ⟨hq_formula, ht_formula⟩

end Omega.Conclusion
