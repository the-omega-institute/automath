import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-schur-pressure-fan-diagram`. A finite separated pressure
support has a unique leading channel with a positive gap to all other channels. -/
theorem paper_pom_schur_pressure_fan_diagram {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (P : ι → ℝ) (hs : s.Nonempty)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → P a ≠ P b) :
    ∃ ν ∈ s, (∀ μ ∈ s, P μ ≤ P ν) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ μ ∈ s, μ ≠ ν → P μ ≤ P ν - ε := by
  classical
  rcases Finset.exists_max_image s P hs with ⟨ν, hνs, hνmax⟩
  refine ⟨ν, hνs, hνmax, ?_⟩
  by_cases hother : (s.erase ν).Nonempty
  · rcases Finset.exists_min_image (s.erase ν) (fun μ => P ν - P μ) hother with
      ⟨μ₀, hμ₀, hμ₀min⟩
    have hμ₀s : μ₀ ∈ s := (Finset.mem_erase.mp hμ₀).2
    have hμ₀_ne : μ₀ ≠ ν := (Finset.mem_erase.mp hμ₀).1
    have hμ₀_lt : P μ₀ < P ν := by
      have hle : P μ₀ ≤ P ν := hνmax μ₀ hμ₀s
      have hne : P μ₀ ≠ P ν := hsep μ₀ hμ₀s ν hνs hμ₀_ne
      exact lt_of_le_of_ne hle hne
    refine ⟨P ν - P μ₀, by linarith, ?_⟩
    intro μ hμs hμ_ne
    have hμerase : μ ∈ s.erase ν := by
      exact Finset.mem_erase.mpr ⟨hμ_ne, hμs⟩
    have hgap_le : P ν - P μ₀ ≤ P ν - P μ := hμ₀min μ hμerase
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro μ hμs hμ_ne
    have hμerase : μ ∈ s.erase ν := Finset.mem_erase.mpr ⟨hμ_ne, hμs⟩
    exact False.elim (hother ⟨μ, hμerase⟩)

end Omega.POM
