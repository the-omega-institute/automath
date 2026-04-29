import Mathlib.Tactic
import Omega.Zeta.XiSmithKernelDirichletEulerSinglePole

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete local Smith profile for a single prime-local Dirichlet factor.  The data record the
finite prefix cutoff `Emax`, the prime parameter, and the Smith residue scale inherited from the
global discrete profile. -/
structure conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data where
  n : Nat
  m : Nat
  d : Fin m → Nat
  conclusion_smith_kernel_dirichlet_euler_rational_local_factors_p : Nat
  conclusion_smith_kernel_dirichlet_euler_rational_local_factors_Emax : Nat
  conclusion_smith_kernel_dirichlet_euler_rational_local_factors_residueScale : Nat

/-- The prefixed local coefficient profile. -/
def conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localCoeff
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) (k : Nat) : ℚ :=
  (D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_p : ℚ) ^ k *
    (D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_residueScale + 1 : Nat)

/-- Finite prefix before the stabilized Smith tail. -/
def conclusion_smith_kernel_dirichlet_euler_rational_local_factors_prefix
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) (T : ℚ) : ℚ :=
  ∑ k ∈ Finset.range D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_Emax,
    conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localCoeff D k * T ^ k

/-- The geometric tail beginning at `Emax`. -/
def conclusion_smith_kernel_dirichlet_euler_rational_local_factors_tail
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) (T : ℚ) : ℚ :=
  conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localCoeff D
      D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_Emax *
    T ^ D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_Emax /
      (1 - (D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_p : ℚ) * T)

/-- Prime-local Smith factor as finite prefix plus stabilized geometric tail. -/
def conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localFactor
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) (T : ℚ) : ℚ :=
  conclusion_smith_kernel_dirichlet_euler_rational_local_factors_prefix D T +
    conclusion_smith_kernel_dirichlet_euler_rational_local_factors_tail D T

/-- Denominator-cleared rational form of the finite-prefix plus geometric-tail local factor. -/
def conclusion_smith_kernel_dirichlet_euler_rational_local_factors_statement
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) : Prop :=
  Omega.Zeta.xi_smith_kernel_dirichlet_euler_single_pole_euler_product D.n D.m D.d ∧
    (∀ q : Nat, Nat.Prime q →
      Omega.Zeta.xi_smith_kernel_dirichlet_euler_single_pole_local_rational D.n D.m D.d q) ∧
    ∀ T : ℚ,
      1 - (D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_p : ℚ) * T ≠ 0 →
        conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localFactor D T =
            conclusion_smith_kernel_dirichlet_euler_rational_local_factors_prefix D T +
              conclusion_smith_kernel_dirichlet_euler_rational_local_factors_tail D T ∧
          (1 - (D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_p : ℚ) * T) *
              conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localFactor D T =
            (1 - (D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_p : ℚ) * T) *
                conclusion_smith_kernel_dirichlet_euler_rational_local_factors_prefix D T +
              conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localCoeff D
                  D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_Emax *
                T ^ D.conclusion_smith_kernel_dirichlet_euler_rational_local_factors_Emax

/-- Paper label: `thm:conclusion-smith-kernel-dirichlet-euler-rational-local-factors`. -/
theorem paper_conclusion_smith_kernel_dirichlet_euler_rational_local_factors
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) :
    conclusion_smith_kernel_dirichlet_euler_rational_local_factors_statement D := by
  rcases Omega.Zeta.paper_xi_smith_kernel_dirichlet_euler_single_pole D.n D.m D.d with
    ⟨heuler, hlocal, _hsingle⟩
  refine ⟨heuler, hlocal, ?_⟩
  intro T hden
  constructor
  · rfl
  · unfold conclusion_smith_kernel_dirichlet_euler_rational_local_factors_localFactor
      conclusion_smith_kernel_dirichlet_euler_rational_local_factors_tail
    field_simp [hden]

end

end Omega.Conclusion
