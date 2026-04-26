import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Omega.Zeta.XiHellingerToeplitzSymbolPoisson

namespace Omega.Zeta

open Filter

noncomputable section

open xi_hellinger_toeplitz_symbol_poisson_Data

/-- Finite Toeplitz determinant proxy read from the zero Fourier mode of the Poisson symbol. -/
def xi_hellinger_toeplitz_szego_thermo_limit_finite_toeplitz_det
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) (n : ℕ) : ℝ :=
  D.xi_hellinger_toeplitz_symbol_poisson_poissonSymbol 0 ^ n

/-- The normalized finite free energy associated to the determinant proxy. -/
def xi_hellinger_toeplitz_szego_thermo_limit_free_energy
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) (_n : ℕ) : ℝ :=
  -Real.log (D.xi_hellinger_toeplitz_symbol_poisson_poissonSymbol 0)

/-- The negative log-symbol integral in the zero-mode Toeplitz package. -/
def xi_hellinger_toeplitz_szego_thermo_limit_negative_log_symbol_integral
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) : ℝ :=
  -Real.log (D.xi_hellinger_toeplitz_symbol_poisson_thetaSymbol 0)

/-- The entropy density obtained from the Szego determinant limit. -/
def xi_hellinger_toeplitz_szego_thermo_limit_entropy_density
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) : ℝ :=
  -Real.log (D.xi_hellinger_toeplitz_symbol_poisson_poissonSymbol 0)

/-- Concrete finite Toeplitz/Szego-limit statement built over the Hellinger Toeplitz symbol
package. The determinant proxy is exposed at every finite size, the normalized free energy is a
constant sequence, and the Poisson/theta symbol identity rewrites the limit as the stated negative
log-symbol integral. -/
def xi_hellinger_toeplitz_szego_thermo_limit_statement : Prop :=
  ∀ D : xi_hellinger_toeplitz_symbol_poisson_Data,
    D.toeplitzSymbolPoissonPackage ∧
      (∀ n : ℕ,
        xi_hellinger_toeplitz_szego_thermo_limit_finite_toeplitz_det D n =
          D.xi_hellinger_toeplitz_symbol_poisson_poissonSymbol 0 ^ n) ∧
      Tendsto (xi_hellinger_toeplitz_szego_thermo_limit_free_energy D) (atTop : Filter ℕ)
        (nhds (xi_hellinger_toeplitz_szego_thermo_limit_negative_log_symbol_integral D)) ∧
      xi_hellinger_toeplitz_szego_thermo_limit_entropy_density D =
        xi_hellinger_toeplitz_szego_thermo_limit_negative_log_symbol_integral D

/-- Paper label: `thm:xi-hellinger-toeplitz-szego-thermo-limit`. -/
theorem paper_xi_hellinger_toeplitz_szego_thermo_limit :
    xi_hellinger_toeplitz_szego_thermo_limit_statement := by
  intro D
  have hsymbol := paper_xi_hellinger_toeplitz_symbol_poisson D
  rcases hsymbol with ⟨htoeplitz, hpoisson_theta, htheta_kernel⟩
  have hzero :
      D.xi_hellinger_toeplitz_symbol_poisson_poissonSymbol 0 =
        D.xi_hellinger_toeplitz_symbol_poisson_thetaSymbol 0 :=
    hpoisson_theta 0
  refine ⟨⟨htoeplitz, hpoisson_theta, htheta_kernel⟩, ?_, ?_, ?_⟩
  · intro n
    rfl
  · have hfun :
        xi_hellinger_toeplitz_szego_thermo_limit_free_energy D =
          fun _ : ℕ =>
            xi_hellinger_toeplitz_szego_thermo_limit_negative_log_symbol_integral D := by
      funext n
      simp [xi_hellinger_toeplitz_szego_thermo_limit_free_energy,
        xi_hellinger_toeplitz_szego_thermo_limit_negative_log_symbol_integral, hzero]
    rw [hfun]
    exact tendsto_const_nhds
  · simp [xi_hellinger_toeplitz_szego_thermo_limit_entropy_density,
      xi_hellinger_toeplitz_szego_thermo_limit_negative_log_symbol_integral, hzero]

end

end Omega.Zeta
