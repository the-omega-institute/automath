import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.POM.LkArcsineLaw

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The half-angle `φ_p = (2p + 1) π / (4k + 2)` attached to the `p`-th `L_k` eigenvalue. -/
def pom_lk_spectral_zeta_dirichlet_phi (k : ℕ) (p : Fin k) : ℝ :=
  Omega.POM.lkHalfOddAngle k p / 2

/-- The `L_k` spectral point written as `4 sin² φ_p`. -/
def pom_lk_spectral_zeta_dirichlet_mu (k : ℕ) (p : Fin k) : ℝ :=
  4 * Real.sin (pom_lk_spectral_zeta_dirichlet_phi k p) ^ 2

/-- Finite-window spectral zeta sum written in the `μ_p = 4 sin² φ_p` normalization. -/
def pom_lk_spectral_zeta_dirichlet_spectral_zeta (k : ℕ) (s : ℝ) : ℝ :=
  ∑ p : Fin k, (pom_lk_spectral_zeta_dirichlet_mu k p) ^ (-s)

/-- The odd Dirichlet model sum attached to the half-odd-angle spectrum. -/
def pom_lk_spectral_zeta_dirichlet_odd_sum (k : ℕ) (s : ℝ) : ℝ :=
  ∑ p : Fin k, ((2 * (p : ℕ) + 1 : ℝ) ^ (-2 * s))

/-- The termwise Dirichlet proxy before factoring out the common scale `((2k+1)/π)^(2s)`. -/
def pom_lk_spectral_zeta_dirichlet_proxy (k : ℕ) (s : ℝ) : ℝ :=
  ∑ p : Fin k, (((2 * k + 1 : ℝ) / Real.pi) ^ (2 * s)) * ((2 * (p : ℕ) + 1 : ℝ) ^ (-2 * s))

/-- The full consecutive Dirichlet cutoff `∑_{n=1}^k n^{-2s}`. -/
def pom_lk_spectral_zeta_dirichlet_full_sum (k : ℕ) (s : ℝ) : ℝ :=
  ∑ p : Fin k, (((p : ℕ) + 1 : ℝ) ^ (-2 * s))

/-- The even Dirichlet cutoff `∑_{n=1}^k (2n)^{-2s}`. -/
def pom_lk_spectral_zeta_dirichlet_even_sum (k : ℕ) (s : ℝ) : ℝ :=
  ∑ p : Fin k, ((2 * (((p : ℕ) + 1 : ℝ)) ^ 1) ^ (-2 * s))

private lemma pom_lk_spectral_zeta_dirichlet_phi_closed_form (k : ℕ) (p : Fin k) :
    pom_lk_spectral_zeta_dirichlet_phi k p =
      ((2 * (p : ℕ) + 1 : ℝ) * Real.pi) / (4 * k + 2) := by
  unfold pom_lk_spectral_zeta_dirichlet_phi Omega.POM.lkHalfOddAngle
  field_simp [two_ne_zero]
  ring

private lemma pom_lk_spectral_zeta_dirichlet_mu_eq_lkEigenvalue (k : ℕ) (p : Fin k) :
    pom_lk_spectral_zeta_dirichlet_mu k p = Omega.POM.lkEigenvalue k p := by
  unfold pom_lk_spectral_zeta_dirichlet_mu pom_lk_spectral_zeta_dirichlet_phi
  unfold Omega.POM.lkEigenvalue
  set θ : ℝ := Omega.POM.lkHalfOddAngle k p / 2
  have hdouble : 2 * θ = Omega.POM.lkHalfOddAngle k p := by
    dsimp [θ]
    ring
  rw [← hdouble, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Paper label: `prop:pom-Lk-spectral-zeta-dirichlet`. This wrapper records the half-angle
closed form `φ_p = (2p+1)π/(4k+2)`, the exact identity `μ_p = 4 sin² φ_p`, the finite odd-mode
Dirichlet proxy obtained by factoring out `((2k+1)/π)^(2s)`, and the exact even/odd scaling
responsible for the `2^{-2s}` Dirichlet factor. -/
theorem paper_pom_lk_spectral_zeta_dirichlet :
    ∀ k : ℕ, ∀ s : ℝ,
      (∀ p : Fin k,
        pom_lk_spectral_zeta_dirichlet_phi k p =
            ((2 * (p : ℕ) + 1 : ℝ) * Real.pi) / (4 * k + 2) ∧
          pom_lk_spectral_zeta_dirichlet_mu k p = Omega.POM.lkEigenvalue k p) ∧
        pom_lk_spectral_zeta_dirichlet_spectral_zeta k s =
          ∑ p : Fin k, (Omega.POM.lkEigenvalue k p) ^ (-s) ∧
        pom_lk_spectral_zeta_dirichlet_proxy k s =
          (((2 * k + 1 : ℝ) / Real.pi) ^ (2 * s)) * pom_lk_spectral_zeta_dirichlet_odd_sum k s ∧
        pom_lk_spectral_zeta_dirichlet_even_sum k s =
          (2 : ℝ) ^ (-2 * s) * pom_lk_spectral_zeta_dirichlet_full_sum k s := by
  intro k s
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    exact ⟨pom_lk_spectral_zeta_dirichlet_phi_closed_form k p,
      pom_lk_spectral_zeta_dirichlet_mu_eq_lkEigenvalue k p⟩
  · unfold pom_lk_spectral_zeta_dirichlet_spectral_zeta
    apply Finset.sum_congr rfl
    intro p hp
    rw [pom_lk_spectral_zeta_dirichlet_mu_eq_lkEigenvalue]
  · rw [pom_lk_spectral_zeta_dirichlet_proxy, pom_lk_spectral_zeta_dirichlet_odd_sum]
    simpa using
      (Finset.mul_sum (s := Finset.univ)
        (f := fun p : Fin k => ((2 * (p : ℕ) + 1 : ℝ) ^ (-2 * s)))
        (a := (((2 * k + 1 : ℝ) / Real.pi) ^ (2 * s)))).symm
  · rw [pom_lk_spectral_zeta_dirichlet_even_sum, pom_lk_spectral_zeta_dirichlet_full_sum]
    calc
      ∑ p : Fin k, (2 * ((((p : ℕ) + 1 : ℝ)) ^ 1)) ^ (-2 * s) =
          ∑ p : Fin k, (2 : ℝ) ^ (-2 * s) * (((p : ℕ) + 1 : ℝ) ^ (-2 * s)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [show (2 * ((((p : ℕ) + 1 : ℝ)) ^ 1)) = (2 : ℝ) * (((p : ℕ) + 1 : ℝ)) by
              simp]
            rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (2 : ℝ) ^ (-2 * s) * ∑ p : Fin k, (((p : ℕ) + 1 : ℝ) ^ (-2 * s)) := by
            simpa using
              (Finset.mul_sum (s := Finset.univ)
                (f := fun p : Fin k => (((p : ℕ) + 1 : ℝ) ^ (-2 * s)))
                (a := ((2 : ℝ) ^ (-2 * s)))).symm

end

end Omega.POM
