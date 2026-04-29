import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.AtomicDefectProny2KappaRecovery
import Omega.Zeta.XiEndpointJensenDefectH12GramKernel

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Positive Fourier-side weight used to package a strict positivity statement for the endpoint
Jensen-defect coefficients. -/
def xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ δ : ℝ) : ℝ :=
  1 + γ ^ (2 : Nat) + δ ^ (2 : Nat)

/-- Auxiliary diagonal Fourier energy used to package the strict positive-definiteness argument. -/
def xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy {J : ℕ} (γ δ m : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J,
    xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ j) (δ j) * m j ^ (2 : Nat)

/-- Finite exponential sample window used for the uniqueness step. -/
def xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample {J : ℕ} (coeff : Fin J → ℂ) (n : ℕ) :
    ℂ :=
  Omega.CircleDimension.atomicDefectSample 1 (fun j : Fin J => (j : ℝ)) coeff n

/-- Packaged strict positivity statement for the endpoint Jensen-defect coefficients. The imported
Gram-kernel package is kept visible, zero auxiliary energy forces vanishing Fourier samples, finite
exponential uniqueness kills the coefficients, and any nonzero coefficient vector has positive
energy. -/
structure xiEndpointJensenDefectH12StrictPDPackage where
  xi_endpoint_jensen_defect_h12_strict_pd_closedFormPackage :
    xiEndpointJensenDefectH12GramKernelPackage
  xi_endpoint_jensen_defect_h12_strict_pd_weightPositive :
    ∀ γ δ : ℝ, 0 < xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight γ δ
  xi_endpoint_jensen_defect_h12_strict_pd_zeroEnergyForcesVanishingFourierData :
    ∀ {J : ℕ} (γ δ m : Fin J → ℝ),
      xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m = 0 →
        ∀ n : Fin J,
          xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample
              (fun j => ((m j : ℝ) : ℂ)) n =
            0
  xi_endpoint_jensen_defect_h12_strict_pd_finiteExponentialUniqueness :
    ∀ {J : ℕ} (coeff : Fin J → ℂ),
      (∀ n : Fin J, xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample coeff n = 0) →
        ∀ j : Fin J, coeff j = 0
  xi_endpoint_jensen_defect_h12_strict_pd_strictPositive :
    ∀ {J : ℕ} (γ δ m : Fin J → ℝ),
      (∃ j : Fin J, m j ≠ 0) →
        0 < xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m

lemma xi_endpoint_jensen_defect_h12_strict_pd_depths_injective {J : ℕ} :
    Function.Injective (fun j : Fin J => (j : ℝ)) := by
  intro i j hij
  apply Fin.ext
  exact Nat.cast_inj.mp hij

lemma xi_endpoint_jensen_defect_h12_strict_pd_energy_zero_implies_coeff_zero {J : ℕ}
    (γ δ m : Fin J → ℝ)
    (henergy : xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m = 0) :
    ∀ j : Fin J, m j = 0 := by
  intro j
  let term : ℝ :=
    xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ j) (δ j) * m j ^ (2 : Nat)
  have hweight_pos :
      0 < xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ j) (δ j) := by
    unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight
    nlinarith
  have hterm_nonneg : 0 ≤ term := by
    dsimp [term]
    positivity
  have hterm_le :
      term ≤ xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m := by
    unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy
    exact Finset.single_le_sum
      (fun k _hk => by
        change
          0 ≤
            xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ k) (δ k) * m k ^ (2 : Nat)
        unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight
        positivity)
      (Finset.mem_univ j)
  have hterm_eq_zero : term = 0 := by
    have hterm_le_zero : term ≤ 0 := by simpa [henergy] using hterm_le
    exact le_antisymm hterm_le_zero hterm_nonneg
  have hm_sq_eq_zero : m j ^ (2 : Nat) = 0 := by
    dsimp [term] at hterm_eq_zero
    have hm_sq_nonneg : 0 ≤ m j ^ (2 : Nat) := by positivity
    nlinarith
  nlinarith

lemma xi_endpoint_jensen_defect_h12_strict_pd_zero_energy_forces_vanishing_fourier_data {J : ℕ}
    (γ δ m : Fin J → ℝ)
    (henergy : xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m = 0) :
    ∀ n : Fin J, xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample
        (fun j => ((m j : ℝ) : ℂ)) n = 0 := by
  have hmzero := xi_endpoint_jensen_defect_h12_strict_pd_energy_zero_implies_coeff_zero γ δ m henergy
  intro n
  unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample
  simp [Omega.CircleDimension.atomicDefectSample, hmzero]

lemma xi_endpoint_jensen_defect_h12_strict_pd_finite_exponential_uniqueness {J : ℕ}
    (coeff : Fin J → ℂ)
    (hvanish : ∀ n : Fin J,
      xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample coeff n = 0) :
    ∀ j : Fin J, coeff j = 0 := by
  have hcoeff_zero :
      coeff = fun _ : Fin J => (0 : ℂ) := by
    refine Omega.CircleDimension.atomicDefectAmplitudes_unique
      (κ := J)
      (deltaStep := 1)
      (depths := fun j : Fin J => (j : ℝ))
      (hdeltaStep := by norm_num)
      (hdepths := xi_endpoint_jensen_defect_h12_strict_pd_depths_injective)
      (amplitudes := fun _ : Fin J => (0 : ℂ))
      (altAmplitudes := coeff)
      ?_
    intro n
    simpa [xi_endpoint_jensen_defect_h12_strict_pd_fourier_sample,
      Omega.CircleDimension.atomicDefectSample] using hvanish n
  intro j
  simpa using congrArg (fun f => f j) hcoeff_zero

lemma xi_endpoint_jensen_defect_h12_strict_pd_strict_positivity {J : ℕ} (γ δ m : Fin J → ℝ)
    (hnonzero : ∃ j : Fin J, m j ≠ 0) :
    0 < xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m := by
  rcases hnonzero with ⟨j, hj⟩
  let term : ℝ :=
    xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ j) (δ j) * m j ^ (2 : Nat)
  have hterm_pos : 0 < term := by
    dsimp [term]
    unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight
    have hm_sq_pos : 0 < m j ^ (2 : Nat) := by
      simpa [pow_two] using sq_pos_of_ne_zero hj
    nlinarith
  have hterm_le :
      term ≤ xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy γ δ m := by
    unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_energy
    exact Finset.single_le_sum
      (fun k _hk => by
        change
          0 ≤
            xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight (γ k) (δ k) * m k ^ (2 : Nat)
        unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight
        positivity)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le hterm_pos hterm_le

/-- The endpoint Jensen-defect closed-form package is available, the auxiliary Fourier energy is
strictly positive on nonzero coefficient vectors, zero energy forces vanishing Fourier samples, and
finite exponential uniqueness then kills the coefficients.
    prop:xi-endpoint-jensen-defect-h12-strict-pd -/
theorem paper_xi_endpoint_jensen_defect_h12_strict_pd : xiEndpointJensenDefectH12StrictPDPackage :=
  by
  refine
    { xi_endpoint_jensen_defect_h12_strict_pd_closedFormPackage :=
        paper_xi_endpoint_jensen_defect_h12_gram_kernel
      xi_endpoint_jensen_defect_h12_strict_pd_weightPositive := ?_
      xi_endpoint_jensen_defect_h12_strict_pd_zeroEnergyForcesVanishingFourierData := ?_
      xi_endpoint_jensen_defect_h12_strict_pd_finiteExponentialUniqueness := ?_
      xi_endpoint_jensen_defect_h12_strict_pd_strictPositive := ?_ }
  · intro γ δ
    unfold xi_endpoint_jensen_defect_h12_strict_pd_fourier_weight
    nlinarith
  · intro J γ δ m henergy
    exact
      xi_endpoint_jensen_defect_h12_strict_pd_zero_energy_forces_vanishing_fourier_data γ δ m
        henergy
  · intro J coeff hvanish
    exact xi_endpoint_jensen_defect_h12_strict_pd_finite_exponential_uniqueness coeff hvanish
  · intro J γ δ m hnonzero
    exact xi_endpoint_jensen_defect_h12_strict_pd_strict_positivity γ δ m hnonzero

end

end Omega.Zeta
