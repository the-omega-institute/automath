import Mathlib.Tactic

namespace Omega.POM

/-- A concrete finite-quotient factorization condition: the representation only depends on the
residue class modulo `q`. -/
def pom_repcont_profinite_colimit_factors_through (q : ℕ) (ρ : ℕ → ℕ) : Prop :=
  ∀ g, ρ g = ρ (g % q)

/-- Toy tensor product on concrete representations, modeled by pointwise addition. -/
def pom_repcont_profinite_colimit_tensor (ρ σ : ℕ → ℕ) : ℕ → ℕ :=
  fun g => ρ g + σ g

/-- A concrete intertwiner between two toy representations. -/
def pom_repcont_profinite_colimit_intertwines (T ρ σ : ℕ → ℕ) : Prop :=
  ∀ g, T (ρ g) = σ g

lemma pom_repcont_profinite_colimit_stable_of_dvd
    {q Q : ℕ} (hdiv : q ∣ Q) {ρ : ℕ → ℕ}
    (hρ : pom_repcont_profinite_colimit_factors_through q ρ) :
    pom_repcont_profinite_colimit_factors_through Q ρ := by
  intro g
  rcases hdiv with ⟨k, rfl⟩
  calc
    ρ g = ρ (g % q) := hρ g
    _ = ρ (g % (q * k) % q) := by rw [← Nat.mod_mul_right_mod g q k]
    _ = ρ (g % (q * k)) := by symm; exact hρ (g % (q * k))

lemma pom_repcont_profinite_colimit_tensor_factors
    {Q : ℕ} {ρ σ : ℕ → ℕ}
    (hρ : pom_repcont_profinite_colimit_factors_through Q ρ)
    (hσ : pom_repcont_profinite_colimit_factors_through Q σ) :
    pom_repcont_profinite_colimit_factors_through Q
      (pom_repcont_profinite_colimit_tensor ρ σ) := by
  intro g
  simp [pom_repcont_profinite_colimit_tensor, hρ g, hσ g]

/-- Paper label: `thm:pom-repcont-profinite-colimit`. In the concrete residue-class model, if two
finite-dimensional continuous representations already factor through finite quotients `qρ` and
`qσ`, then both representations and their tensor product stabilize on the common finite level
`lcm qρ qσ`; any intertwiner between them is therefore already visible on that common level. -/
theorem paper_pom_repcont_profinite_colimit
    (qρ qσ : ℕ) (ρ σ T : ℕ → ℕ)
    (hqρ : 0 < qρ) (hqσ : 0 < qσ)
    (hρ : pom_repcont_profinite_colimit_factors_through qρ ρ)
    (hσ : pom_repcont_profinite_colimit_factors_through qσ σ)
    (hT : pom_repcont_profinite_colimit_intertwines T ρ σ) :
    ∃ Q,
      0 < Q ∧
      qρ ∣ Q ∧
      qσ ∣ Q ∧
      pom_repcont_profinite_colimit_factors_through Q ρ ∧
      pom_repcont_profinite_colimit_factors_through Q σ ∧
      pom_repcont_profinite_colimit_factors_through Q
        (pom_repcont_profinite_colimit_tensor ρ σ) ∧
      pom_repcont_profinite_colimit_intertwines T ρ σ := by
  refine ⟨Nat.lcm qρ qσ, Nat.lcm_pos hqρ hqσ, Nat.dvd_lcm_left qρ qσ, Nat.dvd_lcm_right qρ qσ,
    ?_, ?_, ?_, hT⟩
  · exact pom_repcont_profinite_colimit_stable_of_dvd (Nat.dvd_lcm_left qρ qσ) hρ
  · exact pom_repcont_profinite_colimit_stable_of_dvd (Nat.dvd_lcm_right qρ qσ) hσ
  · exact pom_repcont_profinite_colimit_tensor_factors
      (pom_repcont_profinite_colimit_stable_of_dvd (Nat.dvd_lcm_left qρ qσ) hρ)
      (pom_repcont_profinite_colimit_stable_of_dvd (Nat.dvd_lcm_right qρ qσ) hσ)

end Omega.POM
