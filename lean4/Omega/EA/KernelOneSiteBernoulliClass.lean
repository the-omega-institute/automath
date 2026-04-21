import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.EA.KernelGlobalCarryfreeSpectralTrichotomy
import Omega.EA.KernelGroundStateUniversalityClasses
import Omega.EA.KernelPressureEndpoints

namespace Omega.EA

open Polynomial

noncomputable section

/-- The audited first primitive layer for `K9`. -/
def k9PrimitiveLayer (u : ℝ) : ℝ := 7 + 14 * u

/-- The audited first primitive layer for `K13`. -/
def k13PrimitiveLayer (u : ℝ) : ℝ := 3 + 2 * u + 2 * u ^ 2 + 6 * u ^ 3

/-- The audited first primitive layer for `K21`. -/
def k21PrimitiveLayer (u : ℝ) : ℝ := 1 + 4 * u

/-- Endpoint package for the `K9` pressure interpolation. -/
def k9PressureFamily : KernelPressureFamily where
  zeroWeight := 7
  oneWeight := 21
  monotone_weights := by norm_num

/-- The endpoint value `λ_9(1) = 21`. -/
def k9Endpoint : ℝ := perronRoot k9PressureFamily 1

/-- Audited endpoint values for the other two kernels. -/
def k13Endpoint : ℝ := 13
def k21Endpoint : ℝ := 5

/-- One-site Bernoulli class: affine first primitive layer, one-state carry-free skeleton, and the
endpoint identity `λ(1) = A + B`. -/
def LiesInOneSiteBernoulliClass (primitiveLayer : ℝ → ℝ) (carryfreeCharpoly : Polynomial ℤ)
    (endpoint : ℝ) : Prop :=
  ∃ A : ℤ, ∃ B : ℝ,
    (∀ u, primitiveLayer u = (A : ℝ) + B * u) ∧
      carryfreeCharpoly = Polynomial.X - Polynomial.C A ∧
      endpoint = (A : ℝ) + B

def K9LiesInOneSiteBernoulliClass : Prop :=
  LiesInOneSiteBernoulliClass k9PrimitiveLayer globalAssemblyK9Adjacency.charpoly k9Endpoint

def K13LiesInOneSiteBernoulliClass : Prop :=
  LiesInOneSiteBernoulliClass k13PrimitiveLayer globalAssemblyK13Adjacency.charpoly k13Endpoint

def K21LiesInOneSiteBernoulliClass : Prop :=
  LiesInOneSiteBernoulliClass k21PrimitiveLayer globalAssemblyK21Adjacency.charpoly k21Endpoint

/-- Only `K9` survives the affine/one-state Bernoulli test. -/
def only_K9_lies_in_the_one_site_Bernoulli_class : Prop :=
  K9LiesInOneSiteBernoulliClass ∧
    ¬ K13LiesInOneSiteBernoulliClass ∧
    ¬ K21LiesInOneSiteBernoulliClass

/-- Closed-form thermodynamic functions for `K9`. -/
def k9Pressure (θ : ℝ) : ℝ := Real.log (7 + 14 * Real.exp θ)
def k9PressureDeriv (θ : ℝ) : ℝ := 2 * Real.exp θ / (1 + 2 * Real.exp θ)
def k9PressureVariance (θ : ℝ) : ℝ := 2 * Real.exp θ / (1 + 2 * Real.exp θ) ^ 2

/-- Binary relative-entropy rate function centered at the `K9` equilibrium density. -/
def k9RateFunction (θ₀ α : ℝ) : ℝ :=
  α * Real.log (α / k9PressureDeriv θ₀) +
    (1 - α) * Real.log ((1 - α) / (1 - k9PressureDeriv θ₀))

def K9_closed_form_pressure_curve : Prop :=
  (∀ u, k9PrimitiveLayer u = 7 + 14 * u) ∧
    (∀ θ, k9Pressure θ = Real.log (7 + 14 * Real.exp θ)) ∧
    (∀ θ, k9PressureDeriv θ = 2 * Real.exp θ / (1 + 2 * Real.exp θ)) ∧
    (∀ θ, k9PressureVariance θ = 2 * Real.exp θ / (1 + 2 * Real.exp θ) ^ 2)

def K9_closed_form_rate_function : Prop :=
  ∀ θ₀ α,
    k9RateFunction θ₀ α =
      α * Real.log (α / k9PressureDeriv θ₀) +
        (1 - α) * Real.log ((1 - α) / (1 - k9PressureDeriv θ₀))

lemma k9_endpoint_value : k9Endpoint = 21 := by
  have h := (paper_kernel_pressure_endpoints k9PressureFamily k9PressureFamily).2.1
  simpa [k9Endpoint, k9PressureFamily, oneEndpoint, perronRoot, weightedKernel] using h

lemma k13_not_in_one_site_class : ¬ K13LiesInOneSiteBernoulliClass := by
  intro h
  rcases h with ⟨A, B, hlin, _, _⟩
  have h0 := hlin 0
  have h1 := hlin 1
  have h2 := hlin 2
  norm_num [k13PrimitiveLayer] at h0 h1 h2
  have hB : B = 10 := by linarith
  linarith

lemma k21_not_in_one_site_class : ¬ K21LiesInOneSiteBernoulliClass := by
  intro h
  rcases h with ⟨A, _, _, hchar, _⟩
  rcases paper_kernel_global_carryfree_spectral_trichotomy with
    ⟨_, _, hK21, _, _, _, _⟩
  have hpoly : Polynomial.X ^ 2 - 3 * Polynomial.X + 1 = Polynomial.X - Polynomial.C A := by
    calc
      Polynomial.X ^ 2 - 3 * Polynomial.X + 1 = globalAssemblyK21Adjacency.charpoly := by
        simpa using hK21.symm
      _ = Polynomial.X - Polynomial.C A := hchar
  have h0 := congrArg (fun p : Polynomial ℤ => p.eval 0) hpoly
  have h1 := congrArg (fun p : Polynomial ℤ => p.eval 1) hpoly
  norm_num at h0 h1
  omega

/-- Paper label: `thm:kernel-one-site-bernoulli-class`. -/
theorem paper_kernel_one_site_bernoulli_class :
    only_K9_lies_in_the_one_site_Bernoulli_class ∧
      K9_closed_form_pressure_curve ∧
      K9_closed_form_rate_function := by
  rcases paper_kernel_global_carryfree_spectral_trichotomy with
    ⟨hK9, _, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, k13_not_in_one_site_class, k21_not_in_one_site_class⟩
    refine ⟨7, 14, ?_, ?_, ?_⟩
    · intro u
      simp [k9PrimitiveLayer, mul_comm]
    · simpa using hK9
    · calc
        k9Endpoint = 21 := k9_endpoint_value
        _ = (7 : ℝ) + 14 := by norm_num
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro u
      rfl
    · intro θ
      rfl
    · intro θ
      rfl
    · intro θ
      rfl
  · intro θ₀ α
    rfl

end

end Omega.EA
