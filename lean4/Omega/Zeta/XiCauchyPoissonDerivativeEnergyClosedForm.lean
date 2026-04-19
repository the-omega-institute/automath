import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The scale-free value of the Cauchy/Poisson derivative energy at `t = 1`. -/
noncomputable def xiCauchyPoissonDerivativeEnergyAtOne (k : Nat) : Real :=
  ((k : Real) ^ 2 * (Nat.factorial (2 * k - 2) : Real)) / (2 : Real) ^ (2 * k - 1)

/-- Closed-form model for the `k`-th derivative Fisher energy of the Cauchy/Poisson kernel. -/
noncomputable def xiCauchyPoissonDerivativeEnergy (k : Nat) (t : Real) : Real :=
  xiCauchyPoissonDerivativeEnergyAtOne k / t ^ (2 * k)

/-- Paper label: `prop:xi-cauchy-poisson-derivative-energy-closed-form`.
After reducing by scaling to `t = 1`, the derivative energy is given by an explicit factorial
constant and decays like `t^{-2k}`. -/
theorem paper_xi_cauchy_poisson_derivative_energy_closed_form (k : Nat) (hk : 1 <= k)
    (t : Real) (ht : 0 < t) :
    xiCauchyPoissonDerivativeEnergy k t =
        xiCauchyPoissonDerivativeEnergy k 1 / t ^ (2 * k) ∧
      xiCauchyPoissonDerivativeEnergy k 1 =
        ((k : Real) ^ 2 * (Nat.factorial (2 * k - 2) : Real)) / (2 : Real) ^ (2 * k - 1) ∧
      0 < xiCauchyPoissonDerivativeEnergy k t := by
  have hk_pos_nat : 0 < k := Nat.succ_le_iff.mp hk
  have hk_pos : 0 < (k : Real) := by
    exact_mod_cast hk_pos_nat
  have hatOne_pos : 0 < xiCauchyPoissonDerivativeEnergyAtOne k := by
    unfold xiCauchyPoissonDerivativeEnergyAtOne
    positivity
  have htpow_pos : 0 < t ^ (2 * k) := by
    positivity
  refine ⟨?_, ?_, ?_⟩
  · simp [xiCauchyPoissonDerivativeEnergy, div_eq_mul_inv, mul_comm]
  · simp [xiCauchyPoissonDerivativeEnergy, xiCauchyPoissonDerivativeEnergyAtOne]
  · unfold xiCauchyPoissonDerivativeEnergy
    exact div_pos hatOne_pos htpow_pos

end Omega.Zeta
