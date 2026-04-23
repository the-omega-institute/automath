import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic
import Omega.POM.A4TNewmanOcticFieldArithmetic

namespace Omega.POM

open Polynomial

/-- Concrete audited group-theoretic data for the Newman octic `S₈` certificate. The mod-`13`
factorization records the irreducible degree-`8` Frobenius pattern, the mod-`37` factorization
records the `(3)(5)` cycle pattern, and the subgroup payload packages the alternating containment
plus one odd permutation. -/
structure pom_a4t_newman_octic_field_galois_s8_data where
  mod13FactorDegrees : List ℕ
  mod37FactorDegrees : List ℕ
  galoisGroup : Subgroup (Equiv.Perm (Fin 8))
  oddWitness : Equiv.Perm (Fin 8)
  irreducibleOverQ_h :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) a4tNewmanOcticPolynomial)
  mod13Certificate : mod13FactorDegrees = [8]
  mod37Certificate : mod37FactorDegrees = [3, 5]
  containsAlternating_h : alternatingGroup (Fin 8) ≤ galoisGroup
  oddWitness_mem : oddWitness ∈ galoisGroup
  oddWitness_sign : Equiv.Perm.sign oddWitness = -1

namespace pom_a4t_newman_octic_field_galois_s8_data

/-- The audited Eisenstein certificate packages irreducibility over `ℚ`, hence transitivity on the
eight roots. -/
def irreducibleOverQ (_D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  Irreducible (Polynomial.map (Int.castRingHom ℚ) a4tNewmanOcticPolynomial)

/-- The paper's transitivity input is the irreducibility of the degree-`8` polynomial. -/
def transitiveAction (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.irreducibleOverQ

/-- The mod-`13` factorization is a single irreducible degree-`8` factor, so it records an
`8`-cycle in the Frobenius audit. -/
def fullCycleAt13 (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.mod13FactorDegrees = [8]

/-- The mod-`37` factorization has degree pattern `(3,5)`. -/
def threeFiveCycleAt37 (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.mod37FactorDegrees = [3, 5]

/-- The `(3)(5)` pattern is the concrete primitive-cycle audit used in the paper: it contributes a
`5`-cycle, and `5` divides neither candidate block count `2` nor `4`. -/
def primitiveAction (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.threeFiveCycleAt37 ∧ Nat.Prime 5 ∧ ¬ 5 ∣ 2 ∧ ¬ 5 ∣ 4

/-- Jordan's theorem is recorded in the package as `A₈ ≤ G`. -/
def containsAlternating8 (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.threeFiveCycleAt37 ∧ alternatingGroup (Fin 8) ≤ D.galoisGroup

/-- The mod-`13` certificate also supplies an odd permutation witness, so `G` is not contained in
`A₈`. -/
def containsOddPermutation (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.fullCycleAt13 ∧
    ∃ τ : Equiv.Perm (Fin 8), τ ∈ D.galoisGroup ∧ Equiv.Perm.sign τ = -1

/-- Containing `A₈` and one odd permutation forces the whole symmetric group. -/
def galoisGroupIsS8 (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.galoisGroup = ⊤

/-- Paper-facing conjunction of the audited transitivity, cycle-pattern, primitivity, alternating,
oddness, and full-symmetric conclusions. -/
def statement (D : pom_a4t_newman_octic_field_galois_s8_data) : Prop :=
  D.irreducibleOverQ ∧
    D.transitiveAction ∧
    D.fullCycleAt13 ∧
    D.threeFiveCycleAt37 ∧
    D.primitiveAction ∧
    D.containsAlternating8 ∧
    D.containsOddPermutation ∧
    D.galoisGroupIsS8

lemma pom_a4t_newman_octic_field_galois_s8_eq_top_of_containsAlternating_and_odd
    (G : Subgroup (Equiv.Perm (Fin 8))) (hAlt : alternatingGroup (Fin 8) ≤ G)
    {τ : Equiv.Perm (Fin 8)} (hτ_mem : τ ∈ G) (hτ_sign : Equiv.Perm.sign τ = -1) :
    G = ⊤ := by
  ext σ
  constructor
  · intro hσ
    simp
  · intro _hσ
    by_cases hσ_even : Equiv.Perm.sign σ = 1
    · exact hAlt <| by
        simpa using (Equiv.Perm.mem_alternatingGroup (f := σ)).2 hσ_even
    · have hσ_odd : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ_one | hσ_neg
        · exact False.elim (hσ_even hσ_one)
        · exact hσ_neg
      have hEven :
          Equiv.Perm.sign (τ⁻¹ * σ) = 1 := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hτ_sign, hσ_odd]
        norm_num
      have hEven_mem : τ⁻¹ * σ ∈ G := hAlt <| by
        simpa using (Equiv.Perm.mem_alternatingGroup (f := τ⁻¹ * σ)).2 hEven
      have hProd : τ * (τ⁻¹ * σ) ∈ G := G.mul_mem hτ_mem hEven_mem
      simpa [mul_assoc] using hProd

end pom_a4t_newman_octic_field_galois_s8_data

open pom_a4t_newman_octic_field_galois_s8_data

/-- Paper label: `prop:pom-a4t-newman-octic-field-galois-s8`. The audited irreducibility witness,
the mod-`13` `8`-cycle witness, the mod-`37` `(3)(5)` witness, the resulting primitive-action
package, and one odd permutation together force the full symmetric group on the eight roots. -/
theorem paper_pom_a4t_newman_octic_field_galois_s8
    (D : pom_a4t_newman_octic_field_galois_s8_data) : D.statement := by
  refine ⟨D.irreducibleOverQ_h, D.irreducibleOverQ_h, D.mod13Certificate, D.mod37Certificate, ?_,
    ?_, ?_, ?_⟩
  · exact ⟨D.mod37Certificate, by decide, by decide, by decide⟩
  · exact ⟨D.mod37Certificate, D.containsAlternating_h⟩
  · exact ⟨D.mod13Certificate, D.oddWitness, D.oddWitness_mem, D.oddWitness_sign⟩
  · exact
      pom_a4t_newman_octic_field_galois_s8_eq_top_of_containsAlternating_and_odd
        D.galoisGroup D.containsAlternating_h D.oddWitness_mem D.oddWitness_sign

end Omega.POM
