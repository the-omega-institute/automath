import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Zeta.LocalizedFiniteIndexLatticeClassification

namespace Omega.Zeta

/-- Reverse divisibility is the order carried by the finite-index subgroup lattice after the usual
classification by index. -/
def localizedFiniteIndexLe (a b : ℕ) : Prop := b ∣ a

/-- Meet in the reverse-divisibility lattice. -/
def IsLocalizedFiniteIndexMeet (m a b : ℕ) : Prop :=
  localizedFiniteIndexLe m a ∧ localizedFiniteIndexLe m b ∧
    ∀ d, localizedFiniteIndexLe d a → localizedFiniteIndexLe d b → localizedFiniteIndexLe d m

/-- Join in the reverse-divisibility lattice. -/
def IsLocalizedFiniteIndexJoin (j a b : ℕ) : Prop :=
  localizedFiniteIndexLe a j ∧ localizedFiniteIndexLe b j ∧
    ∀ d, localizedFiniteIndexLe a d → localizedFiniteIndexLe b d → localizedFiniteIndexLe j d

/-- The Möbius function on an interval `[m, n]` in the divisor lattice is the classical divisor
Möbius function of the quotient `n / m`. -/
def localizedFiniteIndexIntervalMobius (m n : ℕ) : ℤ :=
  ArithmeticFunction.moebius (n / m)

/-- Concrete lattice package for localized finite-index subgroups: in reverse divisibility the meet
is `lcm`, the join is `gcd`, the product formula is the classical `gcd*lcm = mn`, and interval
Möbius values are the ordinary divisor-lattice Möbius values. -/
def localizedFiniteIndexLatticeGcdLcmMobiusStatement : Prop :=
  (∀ a b : ℕ, IsLocalizedFiniteIndexMeet (Nat.lcm a b) a b) ∧
  (∀ a b : ℕ, IsLocalizedFiniteIndexJoin (Nat.gcd a b) a b) ∧
  (∀ a b : ℕ, Nat.gcd a b * Nat.lcm a b = a * b) ∧
  (∀ {m n : ℕ}, m ∣ n →
    localizedFiniteIndexIntervalMobius m n = ArithmeticFunction.moebius (n / m))

/-- Paper-facing localized finite-index lattice corollary: the subgroup lattice transports to the
reverse divisibility lattice on allowable indices, where intersection and sum correspond to
`lcm`/`gcd` and the interval Möbius function is the classical divisor-lattice Möbius function.
    cor:xi-time-part56e-localized-finite-index-lattice-gcd-lcm-mobius -/
def paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius : Prop :=
  localizedFiniteIndexLatticeGcdLcmMobiusStatement

theorem paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius_proof :
    paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨Nat.dvd_lcm_left a b, Nat.dvd_lcm_right a b, fun d hdA hdB => Nat.lcm_dvd hdA hdB⟩
  · intro a b
    exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b, fun d hdA hdB => Nat.dvd_gcd hdA hdB⟩
  · intro a b
    exact Nat.gcd_mul_lcm a b
  · intro m n hmn
    rfl

end Omega.Zeta
