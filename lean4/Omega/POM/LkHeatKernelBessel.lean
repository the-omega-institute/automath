import Mathlib
import Omega.POM.LkArcsineLaw

namespace Omega.POM

open Filter Topology

noncomputable section

/-- Paper label: `cor:pom-Lk-heat-kernel-bessel`. -/
theorem paper_pom_lk_heat_kernel_bessel (t : ℝ) (ht : 0 ≤ t) (I0 : ℝ → ℝ)
    (hBessel :
      arcsineAverage (fun μ => Real.exp (-t * μ)) = Real.exp (-2 * t) * I0 (2 * t)) :
    Tendsto (fun k : ℕ => lkEmpiricalAverage k (fun μ => Real.exp (-t * μ))) atTop
        (𝓝 (Real.exp (-2 * t) * I0 (2 * t))) ∧
      Tendsto
        (fun k : ℕ =>
          ((k : ℝ) / (2 * k + 1)) * lkEmpiricalAverage k (fun μ => Real.exp (-t * μ)))
        atTop (𝓝 ((1 / 2) * Real.exp (-2 * t) * I0 (2 * t))) := by
  let _ := ht
  let f : ℝ → ℝ := fun μ => Real.exp (-t * μ)
  have hfun :
      (fun μ : ℝ => Real.exp (-(t * μ))) = fun μ : ℝ => Real.exp (-t * μ) := by
    funext μ
    congr 1
    ring
  have hBessel' :
      arcsineAverage (fun μ => Real.exp (-(t * μ))) = Real.exp (-2 * t) * I0 (2 * t) := by
    rw [hfun]
    exact hBessel
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hbulk :
      Tendsto (fun k : ℕ => lkEmpiricalAverage k f) atTop
        (𝓝 (Real.exp (-2 * t) * I0 (2 * t))) := by
    simpa [f, hBessel'] using paper_pom_Lk_arcsine_law f hf
  have hden_zero :
      Tendsto (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1)) atTop (𝓝 0) := by
    have hden_nat :
        Tendsto (fun k : ℕ => (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      change Tendsto (((fun m : ℕ => (1 : ℝ) / (m : ℝ)) ∘ fun k : ℕ => 2 * k + 1))
        atTop (𝓝 0)
      have hshift : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        filter_upwards [eventually_ge_atTop b] with k hk
        omega
      exact (tendsto_const_div_atTop_nhds_zero_nat 1).comp hshift
    simpa [Nat.cast_add, Nat.cast_mul] using hden_nat
  have hratio :
      Tendsto (fun k : ℕ => (k : ℝ) / (2 * k + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have heq :
        (fun k : ℕ => (k : ℝ) / (2 * k + 1)) =
          fun k : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) := by
      funext k
      have hden : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hden]
      ring
    rw [heq]
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hden_zero))
  refine ⟨hbulk, ?_⟩
  have hscaled :
      Tendsto
        (fun k : ℕ => ((k : ℝ) / (2 * k + 1)) * (Real.exp (-2 * t) * I0 (2 * t)))
        atTop (𝓝 ((1 / 2 : ℝ) * (Real.exp (-2 * t) * I0 (2 * t)))) := by
    exact hratio.mul tendsto_const_nhds
  simpa [f, lkEmpiricalAverage, hBessel', mul_assoc] using hscaled

end

end Omega.POM
