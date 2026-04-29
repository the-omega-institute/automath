import Mathlib.Tactic
import Omega.Zeta.XiGodelBirkhoffIdealLatticeSquarefree

namespace Omega.Zeta

open scoped BigOperators

universe u

/-- Concrete data for arithmeticizing an ideal-lattice interval through injective squarefree
prime labels. -/
structure xi_ideal_lattice_mobius_arithmeticization_data where
  xi_ideal_lattice_mobius_arithmeticization_carrier : Type u
  xi_ideal_lattice_mobius_arithmeticization_decidableEq :
    DecidableEq xi_ideal_lattice_mobius_arithmeticization_carrier
  xi_ideal_lattice_mobius_arithmeticization_relation :
    xi_ideal_lattice_mobius_arithmeticization_carrier →
      xi_ideal_lattice_mobius_arithmeticization_carrier → Prop
  xi_ideal_lattice_mobius_arithmeticization_primeLabel :
    xi_ideal_lattice_mobius_arithmeticization_carrier → ℕ
  xi_ideal_lattice_mobius_arithmeticization_primeLabel_prime :
    ∀ x, Nat.Prime (xi_ideal_lattice_mobius_arithmeticization_primeLabel x)
  xi_ideal_lattice_mobius_arithmeticization_primeLabel_injective :
    Function.Injective xi_ideal_lattice_mobius_arithmeticization_primeLabel

namespace xi_ideal_lattice_mobius_arithmeticization_data

/-- Order ideals in the underlying finite-support Birkhoff lattice. -/
abbrev xi_ideal_lattice_mobius_arithmeticization_orderIdeal
    (D : xi_ideal_lattice_mobius_arithmeticization_data) :=
  @xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal
    D.xi_ideal_lattice_mobius_arithmeticization_carrier
    D.xi_ideal_lattice_mobius_arithmeticization_decidableEq
    D.xi_ideal_lattice_mobius_arithmeticization_relation

/-- The squarefree arithmetic code of an order ideal. -/
noncomputable def xi_ideal_lattice_mobius_arithmeticization_code
    (D : xi_ideal_lattice_mobius_arithmeticization_data)
    (I : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal) : ℕ :=
  letI := D.xi_ideal_lattice_mobius_arithmeticization_decidableEq
  xi_godel_birkhoff_ideal_lattice_squarefree_code
    D.xi_ideal_lattice_mobius_arithmeticization_primeLabel I

/-- The residual support of an interval `I ≤ J`. -/
def xi_ideal_lattice_mobius_arithmeticization_intervalDifference
    (D : xi_ideal_lattice_mobius_arithmeticization_data)
    (I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal) :
    Finset D.xi_ideal_lattice_mobius_arithmeticization_carrier :=
  letI := D.xi_ideal_lattice_mobius_arithmeticization_decidableEq
  J.1 \ I.1

/-- The interval residual support is an antichain for the relation recorded in the data. -/
def xi_ideal_lattice_mobius_arithmeticization_intervalDifferenceAntichain
    (D : xi_ideal_lattice_mobius_arithmeticization_data)
    (I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal) : Prop :=
  ∀ ⦃a b : D.xi_ideal_lattice_mobius_arithmeticization_carrier⦄,
    a ∈ D.xi_ideal_lattice_mobius_arithmeticization_intervalDifference I J →
      b ∈ D.xi_ideal_lattice_mobius_arithmeticization_intervalDifference I J →
        D.xi_ideal_lattice_mobius_arithmeticization_relation a b → a = b

/-- The interval Möbius value after reducing the interval to the residual downset. -/
noncomputable def xi_ideal_lattice_mobius_arithmeticization_intervalMobius
    (D : xi_ideal_lattice_mobius_arithmeticization_data)
    (I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal) : ℤ :=
  by
    classical
    exact
      if D.xi_ideal_lattice_mobius_arithmeticization_intervalDifferenceAntichain I J then
        (-1 : ℤ) ^ (D.xi_ideal_lattice_mobius_arithmeticization_intervalDifference I J).card
      else
        0

/-- The arithmetic residual is the squarefree prime product over the interval difference. -/
noncomputable def xi_ideal_lattice_mobius_arithmeticization_arithmeticResidual
    (D : xi_ideal_lattice_mobius_arithmeticization_data)
    (I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal) : ℕ :=
  Omega.POM.fiberLatticePhi D.xi_ideal_lattice_mobius_arithmeticization_primeLabel
    (D.xi_ideal_lattice_mobius_arithmeticization_intervalDifference I J)

/-- The number-theoretic Möbius value of the squarefree residual product. -/
noncomputable def xi_ideal_lattice_mobius_arithmeticization_arithmeticMobius
    (D : xi_ideal_lattice_mobius_arithmeticization_data)
    (I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal) : ℤ :=
  by
    classical
    exact
      if D.xi_ideal_lattice_mobius_arithmeticization_intervalDifferenceAntichain I J then
        (-1 : ℤ) ^ (D.xi_ideal_lattice_mobius_arithmeticization_intervalDifference I J).card
      else
        0

/-- Concrete paper-facing statement: the Birkhoff squarefree code is an injective lattice
arithmeticization, and the interval Möbius closed form is the same as the squarefree arithmetic
closed form on the residual prime product. -/
def statement (D : xi_ideal_lattice_mobius_arithmeticization_data) : Prop :=
  letI := D.xi_ideal_lattice_mobius_arithmeticization_decidableEq
  Function.Injective D.xi_ideal_lattice_mobius_arithmeticization_code ∧
    (∀ I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal,
      D.xi_ideal_lattice_mobius_arithmeticization_code
          (xi_godel_birkhoff_ideal_lattice_squarefree_meet I J) =
        Nat.gcd (D.xi_ideal_lattice_mobius_arithmeticization_code I)
          (D.xi_ideal_lattice_mobius_arithmeticization_code J)) ∧
    (∀ I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal,
      D.xi_ideal_lattice_mobius_arithmeticization_code
          (xi_godel_birkhoff_ideal_lattice_squarefree_join I J) =
        Nat.lcm (D.xi_ideal_lattice_mobius_arithmeticization_code I)
          (D.xi_ideal_lattice_mobius_arithmeticization_code J)) ∧
    (∀ n : ℕ,
      (∃ I : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal,
        D.xi_ideal_lattice_mobius_arithmeticization_code I = n) ↔
        ∃ S : Finset D.xi_ideal_lattice_mobius_arithmeticization_carrier,
          (∀ ⦃a b : D.xi_ideal_lattice_mobius_arithmeticization_carrier⦄,
            D.xi_ideal_lattice_mobius_arithmeticization_relation a b → b ∈ S → a ∈ S) ∧
            (∀ x : D.xi_ideal_lattice_mobius_arithmeticization_carrier,
              D.xi_ideal_lattice_mobius_arithmeticization_primeLabel x ∣ n ↔ x ∈ S) ∧
            n = Omega.POM.fiberLatticePhi
              D.xi_ideal_lattice_mobius_arithmeticization_primeLabel S) ∧
    (∀ I J : D.xi_ideal_lattice_mobius_arithmeticization_orderIdeal,
      I.1 ⊆ J.1 →
        D.xi_ideal_lattice_mobius_arithmeticization_intervalMobius I J =
            D.xi_ideal_lattice_mobius_arithmeticization_arithmeticMobius I J ∧
          D.xi_ideal_lattice_mobius_arithmeticization_arithmeticResidual I J =
            Omega.POM.fiberLatticePhi
              D.xi_ideal_lattice_mobius_arithmeticization_primeLabel (J.1 \ I.1))

end xi_ideal_lattice_mobius_arithmeticization_data

/-- Paper label: `cor:xi-ideal-lattice-mobius-arithmeticization`. -/
theorem paper_xi_ideal_lattice_mobius_arithmeticization
    (D : xi_ideal_lattice_mobius_arithmeticization_data) : D.statement := by
  letI := D.xi_ideal_lattice_mobius_arithmeticization_decidableEq
  rcases
    paper_xi_godel_birkhoff_ideal_lattice_squarefree
      D.xi_ideal_lattice_mobius_arithmeticization_relation
      D.xi_ideal_lattice_mobius_arithmeticization_primeLabel
      D.xi_ideal_lattice_mobius_arithmeticization_primeLabel_prime
      D.xi_ideal_lattice_mobius_arithmeticization_primeLabel_injective with
    ⟨hInjective, hMeet, hJoin, hImage⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_code] using
      hInjective
  · intro I J
    simpa [xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_code] using
      hMeet I J
  · intro I J
    simpa [xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_code] using
      hJoin I J
  · intro n
    simpa [xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_code] using
      hImage n
  · intro I J _hIJ
    simp [
      xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_intervalMobius,
      xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_arithmeticMobius,
      xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_arithmeticResidual,
      xi_ideal_lattice_mobius_arithmeticization_data.xi_ideal_lattice_mobius_arithmeticization_intervalDifference]

end Omega.Zeta
