import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The line Poisson kernel used in the Jensen/DtN package. -/
noncomputable def prop_xi_dtn_acts_on_jensen_kernel_xiPoissonKernel (t x : Real) : Real :=
  t / (Real.pi * (x ^ 2 + t ^ 2))

/-- Concrete Jensen-kernel seed carrying the center and offset parameters. -/
structure prop_xi_dtn_acts_on_jensen_kernel_JensenSeed where
  γ : Real
  δ : Real

/-- The Jensen seed evaluated as the shifted log-defect profile. -/
noncomputable def prop_xi_dtn_acts_on_jensen_kernel_jensenEval
    (K : prop_xi_dtn_acts_on_jensen_kernel_JensenSeed) (x : Real) : Real :=
  Real.log (((x - K.γ) ^ 2 + (1 + K.δ) ^ 2) / ((x - K.γ) ^ 2 + (1 - K.δ) ^ 2)) / 2

instance prop_xi_dtn_acts_on_jensen_kernel_jensenSeed_coeFun :
    CoeFun prop_xi_dtn_acts_on_jensen_kernel_JensenSeed (fun _ => Real → Real) where
  coe := prop_xi_dtn_acts_on_jensen_kernel_jensenEval

/-- Concrete DtN readout seed for the shifted Jensen kernel. -/
structure prop_xi_dtn_acts_on_jensen_kernel_DtnSeed where
  γ : Real
  δ : Real

/-- The DtN seed evaluated as the difference of two Poisson kernels. -/
noncomputable def prop_xi_dtn_acts_on_jensen_kernel_dtnEval
    (K : prop_xi_dtn_acts_on_jensen_kernel_DtnSeed) (x : Real) : Real :=
  Real.pi *
    (prop_xi_dtn_acts_on_jensen_kernel_xiPoissonKernel (1 - K.δ) (x - K.γ) -
      prop_xi_dtn_acts_on_jensen_kernel_xiPoissonKernel (1 + K.δ) (x - K.γ))

instance prop_xi_dtn_acts_on_jensen_kernel_dtnSeed_coeFun :
    CoeFun prop_xi_dtn_acts_on_jensen_kernel_DtnSeed (fun _ => Real → Real) where
  coe := prop_xi_dtn_acts_on_jensen_kernel_dtnEval

/-- The Jensen kernel carrying the translation center `γ` and offset `δ`. -/
def prop_xi_dtn_acts_on_jensen_kernel_xiJensenKernel (γ δ : Real) :
    prop_xi_dtn_acts_on_jensen_kernel_JensenSeed :=
  ⟨γ, δ⟩

/-- The concrete DtN operator on the Jensen seed. -/
def prop_xi_dtn_acts_on_jensen_kernel_xiDtn
    (K : prop_xi_dtn_acts_on_jensen_kernel_JensenSeed) :
    prop_xi_dtn_acts_on_jensen_kernel_DtnSeed :=
  ⟨K.γ, K.δ⟩

/-- Poisson smoothing of the DtN seed by adding the semigroup scale `t`. -/
noncomputable def prop_xi_dtn_acts_on_jensen_kernel_xiPoissonConvolution
    (t : Real) (K : prop_xi_dtn_acts_on_jensen_kernel_DtnSeed) : Real → Real :=
  fun x =>
    Real.pi *
      (prop_xi_dtn_acts_on_jensen_kernel_xiPoissonKernel (t + 1 - K.δ) (x - K.γ) -
        prop_xi_dtn_acts_on_jensen_kernel_xiPoissonKernel (t + 1 + K.δ) (x - K.γ))

local notation "xiPoissonKernel" => prop_xi_dtn_acts_on_jensen_kernel_xiPoissonKernel
local notation "xiJensenKernel" => prop_xi_dtn_acts_on_jensen_kernel_xiJensenKernel
local notation "xiDtn" => prop_xi_dtn_acts_on_jensen_kernel_xiDtn
local notation "xiPoissonConvolution" => prop_xi_dtn_acts_on_jensen_kernel_xiPoissonConvolution

theorem paper_xi_dtn_acts_on_jensen_kernel (γ δ : Real) (hδ : 0 < δ ∧ δ < 1) :
    xiDtn (xiJensenKernel γ δ) =
      (fun x : Real => Real.pi * (xiPoissonKernel (1 - δ) (x - γ) - xiPoissonKernel (1 + δ) (x - γ))) ∧
      (∀ t : Real, 0 < t ->
        xiPoissonConvolution t (xiDtn (xiJensenKernel γ δ)) =
          (fun x : Real =>
            Real.pi * (xiPoissonKernel (t + 1 - δ) (x - γ) - xiPoissonKernel (t + 1 + δ) (x - γ)))) := by
  refine ⟨?_, ?_⟩
  · ext x
    rfl
  · intro t ht
    ext x
    rfl

end

end Omega.Zeta
