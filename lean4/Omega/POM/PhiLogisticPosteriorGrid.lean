import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Bernoulli likelihood-ratio odds on the golden posterior grid.
    prop:pom-phi-logistic-posterior-grid -/
theorem paper_pom_phi_logistic_posterior_grid (n s : Nat) (hs : s <= n) :
    let phi : Real := Real.goldenRatio
    let p : Real := phi⁻¹
    let q : Real := phi ^ (-2 : Int)
    (p ^ s * q ^ (n - s)) / (q ^ s * p ^ (n - s)) = phi ^ (((2 * s : Nat) : Int) - (n : Int)) := by
  dsimp
  set φ : Real := Real.goldenRatio
  have hφ_pos : 0 < φ := by simpa [φ] using Real.goldenRatio_pos
  have hφ_ne : φ ≠ 0 := ne_of_gt hφ_pos
  have hp_ne : (φ⁻¹ : Real) ≠ 0 := inv_ne_zero hφ_ne
  have hq_ne : (φ ^ (-2 : Int) : Real) ≠ 0 := zpow_ne_zero _ hφ_ne
  have hsplit :
      ((φ⁻¹ : Real) ^ s * (φ ^ (-2 : Int)) ^ (n - s)) /
          ((φ ^ (-2 : Int)) ^ s * (φ⁻¹ : Real) ^ (n - s)) =
        (((φ⁻¹ : Real) / (φ ^ (-2 : Int))) ^ s) * (((φ ^ (-2 : Int)) / (φ⁻¹ : Real)) ^ (n - s)) := by
    calc
      ((φ⁻¹ : Real) ^ s * (φ ^ (-2 : Int)) ^ (n - s)) /
          ((φ ^ (-2 : Int)) ^ s * (φ⁻¹ : Real) ^ (n - s)) =
        (((φ⁻¹ : Real) ^ s) / ((φ ^ (-2 : Int)) ^ s)) *
          (((φ ^ (-2 : Int)) ^ (n - s)) / ((φ⁻¹ : Real) ^ (n - s))) := by
            field_simp [pow_ne_zero _ hp_ne, pow_ne_zero _ hq_ne]
      _ = (((φ⁻¹ : Real) / (φ ^ (-2 : Int))) ^ s) * (((φ ^ (-2 : Int)) / (φ⁻¹ : Real)) ^ (n - s)) := by
            rw [div_pow, div_pow]
  have hratio₁ : (φ⁻¹ : Real) / (φ ^ (-2 : Int)) = φ := by
    field_simp [hφ_ne]
  have hratio₂ : (φ ^ (-2 : Int)) / (φ⁻¹ : Real) = φ⁻¹ := by
    field_simp [hφ_ne]
  have hnegpow : (φ⁻¹ : Real) ^ (n - s) = φ ^ (-((n - s : Nat) : Int)) := by
    calc
      (φ⁻¹ : Real) ^ (n - s) = (φ ^ (n - s))⁻¹ := by rw [inv_pow]
      _ = φ ^ (-((n - s : Nat) : Int)) := by rw [zpow_neg, zpow_natCast]
  rw [hsplit, hratio₁, hratio₂]
  calc
    φ ^ s * φ⁻¹ ^ (n - s) = φ ^ ((s : Nat) : Int) * φ ^ (-((n - s : Nat) : Int)) := by
      rw [← zpow_natCast, hnegpow]
    _ = φ ^ (((s : Nat) : Int) + (-((n - s : Nat) : Int))) := by
      rw [← zpow_add₀ hφ_ne]
    _ = φ ^ (((2 * s : Nat) : Int) - (n : Int)) := by
      congr 1
      omega

end Omega.POM
