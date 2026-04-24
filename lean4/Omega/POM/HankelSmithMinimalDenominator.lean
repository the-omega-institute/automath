import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete Smith data for the rowwise denominator analysis of a Hankel realization. -/
structure pom_hankel_smith_minimal_denominator_data (d : Nat) where
  smithDiagonal : Fin d → Nat
  rowGcd : Fin d → Nat
  denominator : Nat
  rowFactorDvd : ∀ i : Fin d,
    smithDiagonal i / Nat.gcd (smithDiagonal i) (rowGcd i) ∣ denominator

/-- The rowwise minimal denominator imposed by the Smith diagonal entry `s_i` and the row gcd
`g_i`. -/
def pom_hankel_smith_minimal_denominator_row_factor {d : Nat}
    (h : pom_hankel_smith_minimal_denominator_data d) (i : Fin d) : Nat :=
  h.smithDiagonal i / Nat.gcd (h.smithDiagonal i) (h.rowGcd i)

/-- The global minimal denominator obtained by taking the lcm over all Smith rows. -/
noncomputable def pom_hankel_smith_minimal_denominator_lcm {d : Nat}
    (h : pom_hankel_smith_minimal_denominator_data d) : Nat :=
  Finset.lcm Finset.univ (pom_hankel_smith_minimal_denominator_row_factor h)

/-- Rowwise divisibility by the Smith factors is equivalent to divisibility by their lcm, and the
recorded denominator therefore lies above the minimal common clearing factor. -/
def pom_hankel_smith_minimal_denominator_statement (d : Nat)
    (h : pom_hankel_smith_minimal_denominator_data d) : Prop :=
  (∀ i : Fin d, pom_hankel_smith_minimal_denominator_row_factor h i ∣ h.denominator) ∧
    ∀ N : Nat,
      (∀ i : Fin d, pom_hankel_smith_minimal_denominator_row_factor h i ∣ N) ↔
        pom_hankel_smith_minimal_denominator_lcm h ∣ N

/-- Paper label: `thm:pom-hankel-smith-minimal-denominator`. -/
theorem paper_pom_hankel_smith_minimal_denominator (d : Nat)
    (h : pom_hankel_smith_minimal_denominator_data d) :
    pom_hankel_smith_minimal_denominator_statement d h := by
  refine ⟨?_, ?_⟩
  · intro i
    simpa [pom_hankel_smith_minimal_denominator_row_factor] using h.rowFactorDvd i
  · intro N
    constructor
    · intro hN
      exact Finset.lcm_dvd (fun i _ => hN i)
    · intro hN i
      exact dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) hN

end Omega.POM
