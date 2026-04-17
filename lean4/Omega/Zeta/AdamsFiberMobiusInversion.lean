import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

open scoped ArithmeticFunction.Moebius BigOperators

namespace Omega.Zeta

/-- Endpoint-probe mass on the odd fiber over the fixed `2^a`-layer. -/
def adamsEndpointProbeMass (m : ℕ → ℤ) (a u : ℕ) : ℤ :=
  m (2 ^ a * u)

/-- Exact-order mass on the odd fiber over the fixed `2^a`-layer. -/
def adamsExactOrderMass (f : ℕ → ℤ) (a u : ℕ) : ℤ :=
  f (2 ^ a * u)

/-- Odd divisors of `u`. For odd `u` this is the full divisor lattice. -/
def oddDivisors (u : ℕ) : Finset ℕ :=
  u.divisors.filter Odd

lemma oddDivisors_eq_divisors_of_odd {u : ℕ} (hu : Odd u) :
    oddDivisors u = u.divisors := by
  ext d
  constructor
  · intro hd
    have hd' : d ∈ u.divisors.filter Odd := by
      simpa [oddDivisors] using hd
    exact (Finset.mem_filter.mp hd').1
  · intro hd
    have hd' : d ∈ u.divisors.filter Odd := by
      refine Finset.mem_filter.mpr ⟨hd, ?_⟩
      exact Odd.of_dvd_nat hu (Nat.dvd_of_mem_divisors hd)
    simpa [oddDivisors] using hd'

/-- On each odd fiber above `2^a`, decomposing the endpoint mass as a sum of exact-order masses
over odd divisors is equivalent to recovering the exact-order masses by finite Möbius inversion on
the odd-divisor lattice. This is the finite Adams-fiber inversion step used by the endpoint-probe
bookkeeping. -/
theorem paper_xi_adams_fiber_mobius_inversion (m f : ℕ → ℤ) (a : ℕ) :
    (∀ u > 0, Odd u →
      Finset.sum (oddDivisors u) (fun v => adamsExactOrderMass f a v) = adamsEndpointProbeMass m a u) ↔
    (∀ u > 0, Odd u →
      Finset.sum u.divisorsAntidiagonal
          (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass m a x.2) =
        adamsExactOrderMass f a u) := by
  let s : Set ℕ := {u | Odd u}
  have hs : ∀ d u, d ∣ u → u ∈ s → d ∈ s := by
    intro d u hdu hu
    exact Odd.of_dvd_nat hu hdu
  constructor
  · intro h
    have h' : ∀ u > 0, u ∈ s →
        (∑ v ∈ u.divisors, adamsExactOrderMass f a v) = adamsEndpointProbeMass m a u := by
      intro u hu0 hu
      simpa [s, oddDivisors_eq_divisors_of_odd hu] using h u hu0 hu
    exact
      (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℤ) s hs
        (f := fun u => adamsExactOrderMass f a u)
        (g := fun u => adamsEndpointProbeMass m a u)).mp h'
  · intro h
    have h' : ∀ u > 0, u ∈ s →
        (∑ v ∈ u.divisors, adamsExactOrderMass f a v) = adamsEndpointProbeMass m a u :=
      (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℤ) s hs
        (f := fun u => adamsExactOrderMass f a u)
        (g := fun u => adamsEndpointProbeMass m a u)).mpr h
    intro u hu0 hu
    simpa [s, oddDivisors_eq_divisors_of_odd hu] using h' u hu0 hu

end Omega.Zeta
