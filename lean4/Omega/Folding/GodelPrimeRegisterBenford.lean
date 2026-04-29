import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The candidate leading digits in base `b`. -/
def primeRegisterLeadingDigits (b : ℕ) : Finset ℕ :=
  Finset.Icc 1 (b - 1)

/-- The Benford mass attached to the leading digit `d` in base `b`. -/
noncomputable def primeRegisterBenfordMass (b d : ℕ) : ℝ :=
  Real.log (1 + (1 : ℝ) / d) / Real.log b

/-- The exponential decay constant controlling the nontrivial Fourier modes of the Bernoulli
prime-register characteristic function. -/
noncomputable def primeRegisterBenfordDecay (q : ℝ) : ℝ :=
  2 * q * (1 - q)

/-- Paper-facing package for the Benford law of the Gödel prime register: the Bernoulli parameter
produces a strictly positive Fourier decay constant, and every Benford leading-digit mass in base
`b` is positive. -/
def PrimeRegisterBenford (b : ℕ) (q : ℝ) : Prop :=
  0 < primeRegisterBenfordDecay q ∧
    ∀ d ∈ primeRegisterLeadingDigits b, 0 < primeRegisterBenfordMass b d

/-- Paper label: `thm:fold-godel-prime-register-benford`. -/
theorem paper_fold_godel_prime_register_benford
    (b : ℕ) (hb : 2 ≤ b) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : PrimeRegisterBenford b q := by
  refine ⟨?_, ?_⟩
  · unfold primeRegisterBenfordDecay
    nlinarith
  · intro d hd
    have hb' : (1 : ℝ) < b := by
      have hb'' : (2 : ℝ) ≤ b := by
        exact_mod_cast hb
      linarith
    have hlogb : 0 < Real.log b := Real.log_pos hb'
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hd1)
    have hfrac : 0 < (1 : ℝ) / d := one_div_pos.mpr hd0
    have harg : 1 < 1 + (1 : ℝ) / d := by
      linarith
    have hlognum : 0 < Real.log (1 + (1 : ℝ) / d) := Real.log_pos harg
    unfold primeRegisterBenfordMass
    exact div_pos hlognum hlogb

end Omega.Folding
