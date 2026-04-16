import Mathlib.Data.Finsupp.Multiset
import Mathlib.Tactic
import Omega.GU.EllipticGateMinimalRegister

namespace Omega.GU

/-- Prime spectrum read off from finitely supported valuation data. -/
def ellipticGatePrimeSpectrum (v : ℕ →₀ ℕ) : Finset ℕ :=
  v.support

/-- Canonical finitely supported valuation with unit weight on a finite prime spectrum. -/
def valuationOfPrimeSpectrum (S : Finset ℕ) : ℕ →₀ ℕ :=
  S.1.toFinsupp

theorem valuationOfPrimeSpectrum_support (S : Finset ℕ) :
    ellipticGatePrimeSpectrum (valuationOfPrimeSpectrum S) = S := by
  unfold ellipticGatePrimeSpectrum valuationOfPrimeSpectrum
  simpa using Multiset.toFinsupp_support (s := S.1)

/-- Paper-facing gate condition: the gate parameter lies in `(0,1)`, the register bound from the
minimal-register theorem applies, and the gate is rigidly locked to the spectrum size. -/
def IsEllipticGatePrimeSpectrum (c : ℚ) (m : ℕ) (S : Finset ℕ) : Prop :=
  0 < c ∧ c < 1 ∧ S.card ≤ minimalRegisterSize c m ∧ m = S.card

theorem ellipticGatePrimeSpectrum_rigidity {c : ℚ} {m : ℕ} {S : Finset ℕ}
    (h : IsEllipticGatePrimeSpectrum c m S) : m = S.card :=
  h.2.2.2

/-- Finite prime spectra are exactly the prime spectra realized by elliptic gates: the forward
direction packages rigidity and the canonical support valuation, while the converse constructs
`c = 1/2` and `m = |supp(v)|` from finitely supported valuation data and invokes the existing
minimal-register result.
    cor:group-jg-elliptic-gate-prime-spectrum-classification -/
theorem paper_group_jg_elliptic_gate_prime_spectrum_classification (S : Finset ℕ) :
    (∃ c : ℚ, ∃ m : ℕ, IsEllipticGatePrimeSpectrum c m S) ↔
      ∃ v : ℕ →₀ ℕ, ellipticGatePrimeSpectrum v = S := by
  constructor
  · intro h
    rcases h with ⟨c, m, hgate⟩
    let _ := ellipticGatePrimeSpectrum_rigidity hgate
    exact ⟨valuationOfPrimeSpectrum S, valuationOfPrimeSpectrum_support S⟩
  · intro h
    rcases h with ⟨v, hv⟩
    have hcard : v.support.card = S.card := by
      simpa [ellipticGatePrimeSpectrum] using congrArg Finset.card hv
    refine ⟨(1 / 2 : ℚ), v.support.card, ?_⟩
    refine ⟨by norm_num, by norm_num, ?_, ?_⟩
    · rw [hcard]
      simpa [← hcard] using
        (paper_group_jg_elliptic_gate_minimal_register (c := (1 / 2 : ℚ))
          (hc0 := by norm_num) (hc1 := by norm_num) (m := v.support.card))
    · exact hcard

end Omega.GU
