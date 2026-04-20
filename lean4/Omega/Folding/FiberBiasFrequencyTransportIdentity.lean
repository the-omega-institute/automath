import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

noncomputable section

/-- Frequency-side transport equation obtained from the conditional-bias multiplier formula. -/
def frequencyTransportIdentity
    (m M : ℕ) (k : Fin m) (phase : Fin M → Fin m → ℂ) (muHat nuHat : Fin M → ℂ) : Prop :=
  ∀ t,
    (1 + phase t k) * nuHat t =
      (1 / 2 : ℂ) * (phase t k - 1) * muHat t

/-- Spectral weight transported from the characteristic function when the denominator is nonzero.
At a denominator-zero frequency the paper takes the summand to be `0`; here that branch is
available because the theorem separately checks the vanishing hypothesis there. -/
def transportedBiasWeight (z : ℂ) : ℝ :=
  if _h : 1 + z = 0 then 0 else (1 / 4 : ℝ) * ‖(z - 1) / (1 + z)‖ ^ 2

/-- Parseval-style spectral average for the transported conditional bias energy. -/
def spectralAverageEnergyIdentity
    (m M : ℕ) (k : Fin m) (phase : Fin M → Fin m → ℂ) (muHat nuHat : Fin M → ℂ) : Prop :=
  (M : ℝ)⁻¹ * ∑ t : Fin M, ‖nuHat t‖ ^ 2 =
    (M : ℝ)⁻¹ * ∑ t : Fin M, transportedBiasWeight (phase t k) * ‖muHat t‖ ^ 2

theorem paper_fold_fiber_bias_frequency_transport_identity
    (m M : ℕ) (k : Fin m) (phase : Fin M → Fin m → ℂ) (muHat nuHat : Fin M → ℂ)
    (hmu :
      ∀ t,
        muHat t =
          ((2 : ℂ) ^ m)⁻¹ * ∏ j : Fin m, (1 + phase t j))
    (hnu :
      ∀ t,
        nuHat t =
          ((1 / 2 : ℂ) * ((2 : ℂ) ^ m)⁻¹ * (phase t k - 1) *
            Finset.prod (Finset.univ.erase k) (fun j : Fin m => 1 + phase t j)))
    (hzero : ∀ t, 1 + phase t k = 0 → nuHat t = 0) :
    frequencyTransportIdentity m M k phase muHat nuHat ∧
      spectralAverageEnergyIdentity m M k phase muHat nuHat := by
  have htransport : frequencyTransportIdentity m M k phase muHat nuHat := by
    intro t
    rw [hmu t, hnu t]
    have hprod :
        (1 + phase t k) *
            Finset.prod (Finset.univ.erase k) (fun j : Fin m => 1 + phase t j) =
          ∏ j : Fin m, (1 + phase t j) := by
      simpa [mul_comm] using
        (Finset.prod_erase_mul (s := Finset.univ) (f := fun j : Fin m => 1 + phase t j)
          (by simp : k ∈ Finset.univ))
    calc
      (1 + phase t k) *
          ((1 / 2 : ℂ) * ((2 : ℂ) ^ m)⁻¹ * (phase t k - 1) *
            Finset.prod (Finset.univ.erase k) (fun j : Fin m => 1 + phase t j))
          =
          (1 / 2 : ℂ) * (phase t k - 1) *
            (((2 : ℂ) ^ m)⁻¹ * ((1 + phase t k) *
              Finset.prod (Finset.univ.erase k) (fun j : Fin m => 1 + phase t j))) := by ring
      _ =
          (1 / 2 : ℂ) * (phase t k - 1) *
            (((2 : ℂ) ^ m)⁻¹ * ∏ j : Fin m, (1 + phase t j)) := by
              rw [hprod]
  refine ⟨htransport, ?_⟩
  unfold spectralAverageEnergyIdentity
  refine congrArg (fun s : ℝ => (M : ℝ)⁻¹ * s) ?_
  refine Finset.sum_congr rfl ?_
  intro t _
  by_cases hden : 1 + phase t k = 0
  · have hnu0 : nuHat t = 0 := hzero t hden
    have hmu0 : muHat t = 0 := by
      rw [hmu t]
      have hprod :
          (1 + phase t k) *
              Finset.prod (Finset.univ.erase k) (fun j : Fin m => 1 + phase t j) =
            ∏ j : Fin m, (1 + phase t j) := by
        simpa [mul_comm] using
          (Finset.prod_erase_mul (s := Finset.univ) (f := fun j : Fin m => 1 + phase t j)
            (by simp : k ∈ Finset.univ))
      rw [← hprod, hden]
      simp
    simp [transportedBiasWeight, hden, hnu0, hmu0]
  · have hdiv :=
      congrArg (fun z : ℂ => z / (1 + phase t k)) (htransport t)
    have hnu_formula :
        nuHat t =
          ((1 / 2 : ℂ) * ((phase t k - 1) / (1 + phase t k))) * muHat t := by
      simp [hden] at hdiv
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hdiv
    rw [hnu_formula]
    simp [transportedBiasWeight, hden]
    ring_nf

end

end Omega.Folding
