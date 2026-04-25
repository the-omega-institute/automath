import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Pairing

namespace Omega.POM

/-- The prefixed vertex-count spectrum attached to a multiset of component lengths.  A component
of length `n` contributes the shifted Fibonacci count `F_{n+2}`. -/
def pom_fiber_hyperplane_spectrum_invertibility_vertex_count
    (lengths : Multiset ℕ) : Multiset ℕ :=
  lengths.map fun n => Nat.fib (n + 2)

/-- The endpoint theta profile attached to a multiset of component lengths, encoded as natural
pairs of the two endpoint Fibonacci counts. -/
def pom_fiber_hyperplane_spectrum_invertibility_theta_profile
    (lengths : Multiset ℕ) : Multiset ℕ :=
  lengths.map fun n => Nat.pair (Nat.fib (n + 1)) (Nat.fib (n + 2))

lemma pom_fiber_hyperplane_spectrum_invertibility_vertex_count_injective :
    Function.Injective
      (fun n : ℕ => Nat.fib (n + 2)) :=
  Nat.fib_add_two_strictMono.injective

lemma pom_fiber_hyperplane_spectrum_invertibility_theta_profile_injective :
    Function.Injective
      (fun n : ℕ => Nat.pair (Nat.fib (n + 1)) (Nat.fib (n + 2))) := by
  intro a b h
  have hpair := congrArg Nat.unpair h
  have hpair' :
      (Nat.fib (a + 1), Nat.fib (a + 2)) = (Nat.fib (b + 1), Nat.fib (b + 2)) := by
    simpa [Nat.unpair_pair] using hpair
  have hsnd : Nat.fib (a + 2) = Nat.fib (b + 2) := by
    exact congrArg Prod.snd hpair'
  exact Nat.fib_add_two_strictMono.injective hsnd

/-- Paper label: `cor:pom-fiber-hyperplane-spectrum-invertibility`. -/
theorem paper_pom_fiber_hyperplane_spectrum_invertibility
    (lengths lengths' : Multiset ℕ) (hpos : ∀ n ∈ lengths + lengths', 1 ≤ n)
    (hV :
      pom_fiber_hyperplane_spectrum_invertibility_vertex_count lengths =
        pom_fiber_hyperplane_spectrum_invertibility_vertex_count lengths')
    (hTheta :
      pom_fiber_hyperplane_spectrum_invertibility_theta_profile lengths =
        pom_fiber_hyperplane_spectrum_invertibility_theta_profile lengths') :
    lengths = lengths' := by
  have _hpos := hpos
  have _hV := hV
  exact
    Multiset.map_injective
      pom_fiber_hyperplane_spectrum_invertibility_theta_profile_injective
      (by
        simpa [pom_fiber_hyperplane_spectrum_invertibility_theta_profile] using hTheta)

end Omega.POM
