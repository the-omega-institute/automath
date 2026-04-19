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

/-- Concrete package for recovering the even-order exact masses on a fixed `2^(a+1)` layer from
the endpoint masses along the odd fiber. -/
structure AdamsEvenOrderAtomicSpectrumData where
  m : ℕ → ℤ
  f : ℕ → ℤ
  a : ℕ
  endpointDecomposition :
    ∀ u > 0, Odd u →
      Finset.sum (oddDivisors u) (fun v => adamsExactOrderMass f (a + 1) v) =
        adamsEndpointProbeMass m (a + 1) u

/-- Möbius recovery of the exact-order masses on the even layer `2^(a+1)`. -/
def AdamsEvenOrderAtomicSpectrumData.recoveredLayer
    (D : AdamsEvenOrderAtomicSpectrumData) (u : ℕ) : ℤ :=
  Finset.sum u.divisorsAntidiagonal
    (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.m (D.a + 1) x.2)

/-- The odd-fiber masses on the fixed even layer are determined by the endpoint sequence. -/
def AdamsEvenOrderAtomicSpectrumData.layersDetermined
    (D : AdamsEvenOrderAtomicSpectrumData) : Prop :=
  ∀ u > 0, Odd u → adamsExactOrderMass D.f (D.a + 1) u = D.recoveredLayer u

/-- The even-order atomic masses on the layer `2^(a+1)` are determined by the same Möbius
recovery formula. -/
def AdamsEvenOrderAtomicSpectrumData.evenOrderAtomsDetermined
    (D : AdamsEvenOrderAtomicSpectrumData) : Prop :=
  ∀ u > 0, Odd u → D.f (2 ^ (D.a + 1) * u) = D.recoveredLayer u

/-- The recovered even-layer sequence vanishes exactly when the even-order atoms on that layer
vanish. -/
def AdamsEvenOrderAtomicSpectrumData.vanishingIffNoEvenOrderAtoms
    (D : AdamsEvenOrderAtomicSpectrumData) : Prop :=
  (∀ u > 0, Odd u → D.recoveredLayer u = 0) ↔
    (∀ u > 0, Odd u → D.f (2 ^ (D.a + 1) * u) = 0)

/-- On each fixed even layer `2^(a+1)`, Möbius inversion recovers the exact-order masses from the
endpoint sequence, so the even-order atomic spectrum on that layer is uniquely determined; in
particular the recovered sequence is identically zero exactly when there are no even-order atoms
there.
    cor:xi-adams-even-order-atomic-spectrum-determined -/
theorem paper_xi_adams_even_order_atomic_spectrum_determined
    (D : AdamsEvenOrderAtomicSpectrumData) :
    D.layersDetermined ∧ D.evenOrderAtomsDetermined ∧ D.vanishingIffNoEvenOrderAtoms := by
  have hRecovery :
      ∀ u > 0, Odd u → D.recoveredLayer u = adamsExactOrderMass D.f (D.a + 1) u :=
    (paper_xi_adams_fiber_mobius_inversion D.m D.f (D.a + 1)).mp D.endpointDecomposition
  refine ⟨?_, ?_, ?_⟩
  · intro u hu0 hu
    exact (hRecovery u hu0 hu).symm
  · intro u hu0 hu
    simpa [AdamsEvenOrderAtomicSpectrumData.recoveredLayer, adamsExactOrderMass] using
      (hRecovery u hu0 hu).symm
  · constructor
    · intro hZero u hu0 hu
      have hLayerZero : adamsExactOrderMass D.f (D.a + 1) u = 0 := by
        rw [← hRecovery u hu0 hu]
        exact hZero u hu0 hu
      simpa [adamsExactOrderMass] using hLayerZero
    · intro hNoAtoms u hu0 hu
      have hLayerZero : adamsExactOrderMass D.f (D.a + 1) u = 0 := by
        simpa [adamsExactOrderMass] using hNoAtoms u hu0 hu
      rw [hRecovery u hu0 hu]
      exact hLayerZero

end Omega.Zeta
