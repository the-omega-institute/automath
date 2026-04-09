import Mathlib.Tactic

namespace Omega.POM.LeyangMonotoneCouplingPrimeRegister

open Finset

/-- Monotone coupling function `q(t, α) = t / (t + α)`.
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
noncomputable def q (t α : ℝ) : ℝ := t / (t + α)

/-- `q(·, α)` is monotone increasing in `t` (for `α > 0`, `t > 0`).
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
theorem q_monotone (α t₁ t₂ : ℝ) (hα : 0 < α) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) :
    q t₁ α ≤ q t₂ α := by
  unfold q
  have h1 : (0 : ℝ) < t₁ + α := by linarith
  have h2 : (0 : ℝ) < t₂ + α := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [hα, ht₁, ht₁₂]

/-- Inclusion of pointwise indicator: if `q₁ ≤ q₂` and `U ≤ q₁`, then `U ≤ q₂`.
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
theorem indicator_monotone (q₁ q₂ U : ℝ) (hq : q₁ ≤ q₂) (hU : U ≤ q₁) : U ≤ q₂ :=
  le_trans hU hq

/-- Prime register: the product `∏_{j ∈ S} p j`.
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
def primeRegister {ι : Type*} (S : Finset ι) (p : ι → ℕ) : ℕ :=
  ∏ j ∈ S, p j

/-- Subset implies divisibility of prime registers.
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
theorem primeRegister_dvd_of_subset {ι : Type*}
    (S₁ S₂ : Finset ι) (h : S₁ ⊆ S₂) (p : ι → ℕ) :
    primeRegister S₁ p ∣ primeRegister S₂ p := by
  unfold primeRegister
  exact Finset.prod_dvd_prod_of_subset _ _ _ h

/-- Sub-level filter is monotone in `t`.
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
theorem subset_of_t_le {ι : Type*} [Fintype ι]
    (α U : ι → ℝ) (hα : ∀ j, 0 < α j)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) :
    (Finset.univ.filter (fun j => U j ≤ q t₁ (α j))) ⊆
      (Finset.univ.filter (fun j => U j ≤ q t₂ (α j))) := by
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  refine ⟨hj.1, ?_⟩
  exact le_trans hj.2 (q_monotone (α j) t₁ t₂ (hα j) ht₁ ht₁₂)

/-- Paper package: POM fiber Lee-Yang monotone coupling prime register.
    cor:pom-fiber-leyang-monotone-coupling-prime-register -/
theorem paper_pom_fiber_leyang_monotone_coupling_prime_register
    {ι : Type*} [Fintype ι]
    (α U : ι → ℝ) (p : ι → ℕ) (hα : ∀ j, 0 < α j)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) :
    primeRegister (Finset.univ.filter (fun j => U j ≤ q t₁ (α j))) p ∣
      primeRegister (Finset.univ.filter (fun j => U j ≤ q t₂ (α j))) p :=
  primeRegister_dvd_of_subset _ _ (subset_of_t_le α U hα t₁ t₂ ht₁ ht₁₂) p

end Omega.POM.LeyangMonotoneCouplingPrimeRegister
