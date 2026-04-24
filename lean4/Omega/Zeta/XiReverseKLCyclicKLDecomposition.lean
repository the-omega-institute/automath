import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Orbit mass of a positive cyclic sample. -/
def xiOrbitMass {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, x j

/-- Orbit average of a positive cyclic sample. -/
def xiOrbitAverage {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  xiOrbitMass x / (n + 1 : ℝ)

/-- Orbit-averaged discrete weight. -/
def xiOrbitWeight {n : ℕ} (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  x j / xiOrbitMass x

/-- Uniform weight on the `n + 1` cyclic samples. -/
def xiUniformWeight (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

/-- The entropy-gap integrand written in orbit coordinates. -/
def xiReverseKLCyclicGap {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, xiUniformWeight n * (-Real.log (x j) + Real.log (xiOrbitAverage x))

/-- The discrete reverse-KL divergence from the uniform law to the orbit-averaged weights. -/
def xiReverseKLCyclicKL {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, xiUniformWeight n * Real.log (xiUniformWeight n / xiOrbitWeight x j)

private lemma xiOrbitMass_pos {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 < x j) :
    0 < xiOrbitMass x := by
  unfold xiOrbitMass
  have hle : x 0 ≤ ∑ j : Fin (n + 1), x j := by
    exact Finset.single_le_sum (fun j _ => le_of_lt (hx j)) (by simp)
  exact lt_of_lt_of_le (hx 0) hle

/-- Paper label: `thm:xi-reversekl-cyclic-kl-decomposition`. The entropy-gap integrand built from
the cyclic orbit average matches the reverse KL divergence from the uniform law to the explicit
orbit-averaged weights. -/
theorem paper_xi_reversekl_cyclic_kl_decomposition (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < x j) :
    xiReverseKLCyclicGap x = xiReverseKLCyclicKL x := by
  have hmass : 0 < xiOrbitMass x := xiOrbitMass_pos x hx
  have hcard : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have havg : 0 < xiOrbitAverage x := by
    exact div_pos hmass hcard
  unfold xiReverseKLCyclicGap xiReverseKLCyclicKL
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hxj : 0 < x j := hx j
  have hratio :
      xiUniformWeight n / xiOrbitWeight x j = xiOrbitAverage x / x j := by
    unfold xiUniformWeight xiOrbitWeight xiOrbitAverage xiOrbitMass
    field_simp [hmass.ne', hxj.ne']
  rw [hratio, Real.log_div havg.ne' hxj.ne']
  unfold xiUniformWeight
  ring

end

end Omega.Zeta
