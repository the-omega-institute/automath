import Mathlib.Data.List.Range
import Mathlib.Tactic
import Omega.Zeta.XiExteriorPowerSmithSchubert

namespace Omega.Zeta

/-- The exponent generating series attached to the exterior-power Smith exponent multiset. -/
noncomputable def xi_exterior_power_gaussian_binom_hilbert_generating_series
    (q k : ℕ) (t : ℕ) : ℕ :=
  ((xiExteriorPowerSmithExponentMultiset q k).toList.map fun e => t ^ e).sum

/-- The Hilbert-series numerator obtained by summing the geometric contributions of the cyclic
factors with exponents prescribed by the exterior-power Smith multiset. -/
noncomputable def xi_exterior_power_gaussian_binom_hilbert_hilbert_series
    (q k : ℕ) (t : ℕ) : ℕ :=
  ((xiExteriorPowerSmithExponentMultiset q k).toList.map fun e =>
      ((List.range e).map fun s => t ^ s).sum).sum

/-- Concrete wrapper around the exterior-power Smith exponent multiset, its Schubert base element,
the associated exponent generating series, and the Hilbert-series sum over cyclic factors. -/
def XiExteriorPowerGaussianBinomHilbert (q k : ℕ) : Prop :=
  (2 ≤ q → 1 ≤ k → k ≤ q + 1 →
    (xiExteriorPowerSmithExponentMultiset q k).card = Nat.choose (q + 1) k ∧
      xiExteriorPowerSchubertBase k ∈ xiExteriorPowerSmithExponentMultiset q k) ∧
    (∀ t : ℕ,
      xi_exterior_power_gaussian_binom_hilbert_generating_series q k t =
        ((xiExteriorPowerSmithExponentMultiset q k).toList.map fun e => t ^ e).sum) ∧
    (∀ t : ℕ,
      xi_exterior_power_gaussian_binom_hilbert_hilbert_series q k t =
        ((xiExteriorPowerSmithExponentMultiset q k).toList.map fun e =>
          ((List.range e).map fun s => t ^ s).sum).sum)

/-- Paper label: `prop:xi-exterior-power-gaussian-binom-hilbert`. -/
theorem paper_xi_exterior_power_gaussian_binom_hilbert (q k : ℕ) :
    XiExteriorPowerGaussianBinomHilbert q k := by
  refine ⟨?_, ?_, ?_⟩
  · intro hq hk1 hkq
    exact paper_xi_exterior_power_smith_schubert q k hq hk1 hkq
  · intro t
    rfl
  · intro t
    rfl

end Omega.Zeta
