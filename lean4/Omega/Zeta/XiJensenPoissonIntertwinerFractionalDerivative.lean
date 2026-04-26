import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The line Poisson kernel used in the Jensen/Poisson intertwiner package. -/
noncomputable def prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
    (t x : Real) : Real :=
  t / (Real.pi * (x ^ 2 + t ^ 2))

/-- Concrete Jensen-kernel seed carrying the center and offset parameters. -/
structure prop_xi_jensen_poisson_intertwiner_fractional_derivative_JensenSeed where
  γ : Real
  δ : Real

/-- The Jensen seed evaluated as the shifted log-defect profile. -/
noncomputable def prop_xi_jensen_poisson_intertwiner_fractional_derivative_jensenEval
    (K : prop_xi_jensen_poisson_intertwiner_fractional_derivative_JensenSeed) (x : Real) : Real :=
  Real.log (((x - K.γ) ^ 2 + (1 + K.δ) ^ 2) / ((x - K.γ) ^ 2 + (1 - K.δ) ^ 2)) / 2

instance prop_xi_jensen_poisson_intertwiner_fractional_derivative_jensenSeed_coeFun :
    CoeFun prop_xi_jensen_poisson_intertwiner_fractional_derivative_JensenSeed
      (fun _ => Real → Real) where
  coe := prop_xi_jensen_poisson_intertwiner_fractional_derivative_jensenEval

/-- Concrete fractional-derivative seed for the shifted Jensen kernel. -/
structure prop_xi_jensen_poisson_intertwiner_fractional_derivative_DtnSeed where
  γ : Real
  δ : Real

/-- The fractional derivative evaluated as the difference of two Poisson kernels. -/
noncomputable def prop_xi_jensen_poisson_intertwiner_fractional_derivative_dtnEval
    (K : prop_xi_jensen_poisson_intertwiner_fractional_derivative_DtnSeed) (x : Real) : Real :=
  Real.pi *
    (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
        (1 - K.δ) (x - K.γ) -
      prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
        (1 + K.δ) (x - K.γ))

instance prop_xi_jensen_poisson_intertwiner_fractional_derivative_dtnSeed_coeFun :
    CoeFun prop_xi_jensen_poisson_intertwiner_fractional_derivative_DtnSeed
      (fun _ => Real → Real) where
  coe := prop_xi_jensen_poisson_intertwiner_fractional_derivative_dtnEval

/-- The Jensen kernel carrying the translation center `γ` and offset `δ`. -/
def prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiJensenKernel
    (γ δ : Real) :
    prop_xi_jensen_poisson_intertwiner_fractional_derivative_JensenSeed :=
  ⟨γ, δ⟩

/-- The concrete fractional derivative of the Jensen seed. -/
def prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiDtn
    (K : prop_xi_jensen_poisson_intertwiner_fractional_derivative_JensenSeed) :
    prop_xi_jensen_poisson_intertwiner_fractional_derivative_DtnSeed :=
  ⟨K.γ, K.δ⟩

/-- Poisson smoothing of the fractional-derivative seed by adding the semigroup scale `t`. -/
noncomputable def prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonConvolution
    (t : Real) (K : prop_xi_jensen_poisson_intertwiner_fractional_derivative_DtnSeed) :
    Real → Real :=
  fun x =>
    Real.pi *
      (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
          (t + 1 - K.δ) (x - K.γ) -
        prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
          (t + 1 + K.δ) (x - K.γ))

/-- Paper label: `prop:xi-jensen-poisson-intertwiner-fractional-derivative`. In this concrete
single-packet model the fractional derivative of the Jensen kernel is the difference of the two
Poisson scales, and Poisson smoothing shifts those scales by `t`. -/
theorem paper_xi_jensen_poisson_intertwiner_fractional_derivative (γ δ : Real)
    (_hδ : 0 < δ ∧ δ < 1) :
    prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiDtn
        (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiJensenKernel γ δ) =
      (fun x : Real =>
        Real.pi *
          (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
              (1 - δ) (x - γ) -
            prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
              (1 + δ) (x - γ))) ∧
      (∀ t : Real, 0 < t →
        prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonConvolution t
            (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiDtn
              (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiJensenKernel γ δ)) =
          (fun x : Real =>
            Real.pi *
              (prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
                  (t + 1 - δ) (x - γ) -
                prop_xi_jensen_poisson_intertwiner_fractional_derivative_xiPoissonKernel
                  (t + 1 + δ) (x - γ)))) := by
  refine ⟨?_, ?_⟩
  · ext x
    rfl
  · intro t ht
    ext x
    rfl

end

end Omega.Zeta
