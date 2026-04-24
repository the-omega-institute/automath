import Mathlib.Tactic
import Omega.Zeta.XiToeplitzDetVerblunsky
import Omega.Zeta.XiVerblunskyFromLocalJet

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The finite CMV/Verblunsky prefix determined directly by the local jet. -/
def xiFiniteCMVPrefix (ell : ℕ → ℝ) (N : ℕ) : Fin N → ℝ :=
  fun i => xiVerblunskyFromJet ell i

/-- The finite Toeplitz determinant certificate induced by the jet-determined Verblunsky prefix. -/
def xiToeplitzDetDataFromJet (ell : ℕ → ℝ) (N : ℕ) (delta0 : ℝ) (hdelta0 : 0 < delta0) :
    XiToeplitzDetVerblunskyData where
  steps := N
  delta0 := delta0
  hdelta0 := hdelta0
  alpha := xiFiniteCMVPrefix ell N

/-- The first `N + 1` Toeplitz determinants read off from the jet-determined finite CMV data. -/
def xiFiniteToeplitzDetPrefix
    (ell : ℕ → ℝ) (N : ℕ) (delta0 : ℝ) (hdelta0 : 0 < delta0) : Fin (N + 1) → ℝ :=
  fun i => (xiToeplitzDetDataFromJet ell N delta0 hdelta0).toeplitzDet i

/-- The truncated failure set obtained by checking the jet-determined Verblunsky prefix. -/
def xiJetFailureSet (ell : ℕ → ℝ) (N : ℕ) : Set ℕ :=
  {m | ∃ j < N, m = j + 1 ∧ 1 ≤ |xiVerblunskyFromJet ell j|}

/-- Paper label: `thm:xi-local-jet-determines-finite-cmv-and-toeplitz-certificate`. The local jet
determines the finite CMV prefix, hence the finite Toeplitz determinant certificate, and the first
bad Verblunsky index seen in the truncation is exactly the first nonpositive Toeplitz determinant
index. -/
theorem paper_xi_local_jet_determines_finite_cmv_and_toeplitz_certificate
    (ell coeff : ℕ → ℝ)
    (hcoeff0 : coeff 0 = -ell 1)
    (hcoeff1 : coeff 1 = -ell 2)
    (hcoeff2 : coeff 2 = ell 2 - ell 3)
    (hcoeff0_pos : 0 < coeff 0)
    (N : ℕ) (delta0 : ℝ) (hdelta0 : 0 < delta0) :
    let α := xiFiniteCMVPrefix ell N
    let Δ := xiFiniteToeplitzDetPrefix ell N delta0 hdelta0
    let D := xiToeplitzDetDataFromJet ell N delta0 hdelta0
    xiVerblunskyFromJet ell 0 = coeff 1 / coeff 0 ∧
      xiVerblunskyFromJet ell 1 =
        (coeff 0 * coeff 2 - coeff 1 ^ 2) / (coeff 0 ^ 2 - coeff 1 ^ 2) ∧
      (∀ j : Fin N, α j = xiVerblunskyFromJet ell j) ∧
      (∀ m : Fin (N + 1),
        Δ m = delta0 * Finset.prod (Finset.range m) D.stepFactor) ∧
      D.detProductFactorization ∧
      D.minimalFailureIndexControl ∧
      D.failureSet = xiJetFailureSet ell N := by
  let J : XiVerblunskyLocalJetData :=
    { ell := ell
      coeff := coeff
      coeff_zero := hcoeff0
      coeff_one := hcoeff1
      coeff_two := hcoeff2
      coeff_zero_pos := hcoeff0_pos }
  have hJet := paper_xi_verblunsky_from_local_jet J
  rcases hJet with ⟨_, hαcoeff0, hαcoeff1, _, _, hα0, hα1, _⟩
  let D := xiToeplitzDetDataFromJet ell N delta0 hdelta0
  have hToeplitz := paper_xi_toeplitz_det_verblunsky D
  refine ⟨?_, ?_, ?_, ?_, hToeplitz.1, hToeplitz.2, ?_⟩
  · calc
      xiVerblunskyFromJet ell 0 = xiVerblunskyFromCoeffs coeff 0 := hα0.symm
      _ = coeff 1 / coeff 0 := hαcoeff0
  · calc
      xiVerblunskyFromJet ell 1 = xiVerblunskyFromCoeffs coeff 1 := hα1.symm
      _ = (coeff 0 * coeff 2 - coeff 1 ^ 2) / (coeff 0 ^ 2 - coeff 1 ^ 2) := hαcoeff1
  · intro j
    rfl
  · intro m
    exact D.toeplitzDet_product m
  · ext m
    constructor
    · intro hm
      rcases hm with ⟨j, hj, rfl, hjbad⟩
      have hj' : j < N := by simpa [D, xiToeplitzDetDataFromJet] using hj
      refine ⟨j, hj', rfl, ?_⟩
      simpa [D, xiToeplitzDetDataFromJet, XiToeplitzDetVerblunskyData.alphaAt, xiFiniteCMVPrefix,
        if_pos hj'] using hjbad
    · intro hm
      rcases hm with ⟨j, hj, rfl, hjbad⟩
      refine ⟨j, hj, rfl, ?_⟩
      simpa [D, xiToeplitzDetDataFromJet, XiToeplitzDetVerblunskyData.alphaAt, xiFiniteCMVPrefix,
        if_pos hj] using hjbad

end

end Omega.Zeta
