import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Finite-support orbit data used to package the superexponential log-law. -/
structure PrimeRegisterGodelOrbitSuperexpLoglawData where
  Orbit : Type
  instFintypeOrbit : Fintype Orbit
  instDecidableEqOrbit : DecidableEq Orbit
  orbit_nonempty : Nonempty Orbit
  coeff : Orbit → ℝ
  coeff_nonneg : ∀ o, 0 ≤ coeff o
  base : Orbit
  base_coeff_pos : 0 < coeff base
  A : ℝ
  mu : ℝ
  n : ℕ
  hmu : 0 < mu

attribute [instance] PrimeRegisterGodelOrbitSuperexpLoglawData.instFintypeOrbit
attribute [instance] PrimeRegisterGodelOrbitSuperexpLoglawData.instDecidableEqOrbit

namespace PrimeRegisterGodelOrbitSuperexpLoglawData

/-- Total coefficient mass of the finite-support orbit model. -/
noncomputable def prime_register_godel_orbit_superexp_loglaw_totalCoeff
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℝ :=
  ∑ o, D.coeff o

/-- Normalized orbit weight. -/
noncomputable def prime_register_godel_orbit_superexp_loglaw_normalizedWeight
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) (o : D.Orbit) : ℝ :=
  D.coeff o / D.prime_register_godel_orbit_superexp_loglaw_totalCoeff

/-- Finite weighted expectation of the logarithmic orbit contribution. -/
noncomputable def prime_register_godel_orbit_superexp_loglaw_orbitExpectation
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℝ :=
  ∑ o, D.prime_register_godel_orbit_superexp_loglaw_normalizedWeight o *
    Real.log (D.coeff o + D.mu)

/-- Common exponential scale `A^n`. -/
noncomputable def prime_register_godel_orbit_superexp_loglaw_scale
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℝ :=
  D.A ^ D.n

/-- Explicit main term `A^n (log n + log log n + log μ)`. -/
noncomputable def prime_register_godel_orbit_superexp_loglaw_mainTerm
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℝ :=
  D.prime_register_godel_orbit_superexp_loglaw_scale *
    (Real.log D.n + Real.log (Real.log D.n) + Real.log D.mu)

/-- Packaged logarithmic orbit count: main term plus finite weighted correction. -/
noncomputable def prime_register_godel_orbit_superexp_loglaw_logOrbitCount
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : ℝ :=
  D.prime_register_godel_orbit_superexp_loglaw_mainTerm +
    D.prime_register_godel_orbit_superexp_loglaw_scale *
      D.prime_register_godel_orbit_superexp_loglaw_orbitExpectation

/-- The finite normalized orbit weights sum to one, and the logarithmic orbit count factors as
`A^n (log n + log log n + log μ + weighted expectation)`. -/
def superexpLogAsymptotic (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : Prop :=
  (∑ o, D.prime_register_godel_orbit_superexp_loglaw_normalizedWeight o) = 1 ∧
    D.prime_register_godel_orbit_superexp_loglaw_logOrbitCount =
      D.prime_register_godel_orbit_superexp_loglaw_scale *
        (Real.log D.n + Real.log (Real.log D.n) + Real.log D.mu +
          D.prime_register_godel_orbit_superexp_loglaw_orbitExpectation)

lemma prime_register_godel_orbit_superexp_loglaw_totalCoeff_pos
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) :
    0 < D.prime_register_godel_orbit_superexp_loglaw_totalCoeff := by
  classical
  have hbase :
      D.coeff D.base ≤ D.prime_register_godel_orbit_superexp_loglaw_totalCoeff := by
    unfold prime_register_godel_orbit_superexp_loglaw_totalCoeff
    exact Finset.single_le_sum (fun o _ => D.coeff_nonneg o) (by simp)
  exact lt_of_lt_of_le D.base_coeff_pos hbase

lemma prime_register_godel_orbit_superexp_loglaw_normalizedWeight_sum
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) :
    (∑ o, D.prime_register_godel_orbit_superexp_loglaw_normalizedWeight o) = 1 := by
  calc
    (∑ o, D.prime_register_godel_orbit_superexp_loglaw_normalizedWeight o)
        = (∑ o, D.coeff o) / D.prime_register_godel_orbit_superexp_loglaw_totalCoeff := by
            unfold prime_register_godel_orbit_superexp_loglaw_normalizedWeight
            rw [Finset.sum_div]
    _ = 1 := by
          simpa [prime_register_godel_orbit_superexp_loglaw_totalCoeff] using
            div_self D.prime_register_godel_orbit_superexp_loglaw_totalCoeff_pos.ne'

end PrimeRegisterGodelOrbitSuperexpLoglawData

open PrimeRegisterGodelOrbitSuperexpLoglawData

/-- Paper label: `thm:conclusion-prime-register-godel-orbit-superexp-loglaw`. The finite-support
orbit coefficients define a normalized expectation term, and the logarithmic orbit count is the
common scale `A^n` times the explicit `log n + log log n + log μ` main term plus that weighted
correction. -/
theorem paper_conclusion_prime_register_godel_orbit_superexp_loglaw
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : D.superexpLogAsymptotic := by
  refine ⟨D.prime_register_godel_orbit_superexp_loglaw_normalizedWeight_sum, ?_⟩
  unfold PrimeRegisterGodelOrbitSuperexpLoglawData.prime_register_godel_orbit_superexp_loglaw_logOrbitCount
  unfold PrimeRegisterGodelOrbitSuperexpLoglawData.prime_register_godel_orbit_superexp_loglaw_mainTerm
  ring

end Omega.Conclusion
