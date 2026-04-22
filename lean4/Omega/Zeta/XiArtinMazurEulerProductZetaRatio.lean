import Mathlib.Tactic
import Omega.Zeta.XiSolenoidPArtinMazurZeta

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The single-prime Artin--Mazur factor evaluated at `p^{-s}`. -/
def xi_artin_mazur_euler_product_zeta_ratio_local_factor (p s : ℕ) : ℚ :=
  xi_solenoid_p_artin_mazur_zeta_function p (((p : ℚ) ^ s)⁻¹)

/-- The same local factor rewritten as the standard Euler ratio
`(1 - p^{-s}) / (1 - p · p^{-s})`. -/
def xi_artin_mazur_euler_product_zeta_ratio_zeta_factor (p s : ℕ) : ℚ :=
  (1 - ((p : ℚ) ^ s)⁻¹) / (1 - (p : ℚ) * ((p : ℚ) ^ s)⁻¹)

/-- Finite Euler product built from the single-prime Artin--Mazur factors. -/
def xi_artin_mazur_euler_product_zeta_ratio_product (P : Finset ℕ) (s : ℕ) : ℚ :=
  P.prod fun p => xi_artin_mazur_euler_product_zeta_ratio_local_factor p s

/-- Paper label: `cor:xi-artin-mazur-euler-product-zeta-ratio`.
Evaluating each single-prime Artin--Mazur factor at `p^{-s}` gives the local Euler ratio, and the
finite product is exactly the corresponding Euler product for the shifted zeta ratio. -/
theorem paper_xi_artin_mazur_euler_product_zeta_ratio
    (P : Finset ℕ) (s : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∀ p ∈ P,
      xi_artin_mazur_euler_product_zeta_ratio_local_factor p s =
        xi_artin_mazur_euler_product_zeta_ratio_zeta_factor p s) ∧
      xi_artin_mazur_euler_product_zeta_ratio_product P s =
        P.prod (fun p => xi_artin_mazur_euler_product_zeta_ratio_zeta_factor p s) := by
  have hLocal :
      ∀ p ∈ P,
        xi_artin_mazur_euler_product_zeta_ratio_local_factor p s =
          xi_artin_mazur_euler_product_zeta_ratio_zeta_factor p s := by
    intro p hp
    have hFactor := (paper_xi_solenoid_p_artin_mazur_zeta p (hP p hp)).2 (((p : ℚ) ^ s)⁻¹)
    simpa [xi_artin_mazur_euler_product_zeta_ratio_local_factor,
      xi_artin_mazur_euler_product_zeta_ratio_zeta_factor] using hFactor
  refine ⟨hLocal, ?_⟩
  unfold xi_artin_mazur_euler_product_zeta_ratio_product
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact hLocal p hp

end

end Omega.Zeta
