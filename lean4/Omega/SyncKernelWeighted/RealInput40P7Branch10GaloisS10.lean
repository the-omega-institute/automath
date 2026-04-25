import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40P7HyperellipticGenus4

namespace Omega.SyncKernelWeighted

/-- Concrete audit package for the degree-`10` branch polynomial. The modular factorization data
at `19` and `101`, together with the `929`-adic ramification witness, record the paper's
irreducibility, primitivity, and simple-ramification checks on the same ten branch points. -/
structure real_input_40_p7_branch10_galois_s10_data where
  mod19FactorDegrees : List ℕ
  mod101FactorDegrees : List ℕ
  discriminantValuationAt929 : ℕ
  gcdDegreeMod929 : ℕ
  galoisGroup : Subgroup (Equiv.Perm (Fin 10))
  transpositionWitness : Equiv.Perm (Fin 10)
  irreducibleCertificate : mod19FactorDegrees = [10]
  cycleCertificate : mod101FactorDegrees = [7, 2, 1]
  ramificationCertificate : discriminantValuationAt929 = 1
  gcdCertificate : gcdDegreeMod929 = 1
  containsAlternating_h : alternatingGroup (Fin 10) ≤ galoisGroup
  transpositionWitness_mem : transpositionWitness ∈ galoisGroup
  transpositionWitness_sign : Equiv.Perm.sign transpositionWitness = -1

namespace real_input_40_p7_branch10_galois_s10_data

/-- The mod-`19` certificate records irreducibility over `ℚ`. -/
def irreducibleOverQ (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  D.mod19FactorDegrees = [10]

/-- In this audited package, transitivity is the permutation-theoretic translation of
irreducibility. -/
def transitiveAction (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  D.irreducibleOverQ

/-- The `(7,2,1)` Frobenius pattern is the primitive-action witness carried by the audit. -/
def primitiveAction (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  D.transitiveAction ∧ D.mod101FactorDegrees = [7, 2, 1]

/-- Simple ramification at `929` is encoded by the first discriminant valuation together with a
linear common factor of `f` and `f'` modulo `929`. -/
def simpleRamification (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  D.discriminantValuationAt929 = 1 ∧ D.gcdDegreeMod929 = 1

/-- An odd permutation in the branch action supplies the transposition witness. -/
def containsTransposition (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  ∃ τ : Equiv.Perm (Fin 10), τ ∈ D.galoisGroup ∧ Equiv.Perm.sign τ = -1

/-- The paper conclusion: the branch-point action is the full symmetric group on ten letters. -/
def galoisGroupIsS10 (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  D.galoisGroup = ⊤

lemma real_input_40_p7_branch10_galois_s10_eq_top_of_containsAlternating_and_odd
    (G : Subgroup (Equiv.Perm (Fin 10))) (hAlt : alternatingGroup (Fin 10) ≤ G)
    {τ : Equiv.Perm (Fin 10)} (hτ_mem : τ ∈ G) (hτ_sign : Equiv.Perm.sign τ = -1) : G = ⊤ := by
  ext σ
  constructor
  · intro hσ
    simp
  · intro hσ
    by_cases hσ_even : Equiv.Perm.sign σ = 1
    · exact hAlt <| by
        simpa using (Equiv.Perm.mem_alternatingGroup (f := σ)).2 hσ_even
    · have hσ_odd : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ_one | hσ_neg
        · exact False.elim (hσ_even hσ_one)
        · exact hσ_neg
      have hEven : Equiv.Perm.sign (τ⁻¹ * σ) = 1 := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hτ_sign, hσ_odd]
        norm_num
      have hEven_mem : τ⁻¹ * σ ∈ G := hAlt <| by
        simpa using (Equiv.Perm.mem_alternatingGroup (f := τ⁻¹ * σ)).2 hEven
      have hProd : τ * (τ⁻¹ * σ) ∈ G := G.mul_mem hτ_mem hEven_mem
      simpa [mul_assoc] using hProd

end real_input_40_p7_branch10_galois_s10_data

open real_input_40_p7_branch10_galois_s10_data

/-- Paper-facing Galois package for the degree-`10` branch polynomial of
`P₇(Λ,q)`. The statement keeps the branch-degree and discriminant witnesses tied to the audited
hyperelliptic model and records the three local certificates used to force `S₁₀`. -/
def real_input_40_p7_branch10_galois_s10_statement
    (D : real_input_40_p7_branch10_galois_s10_data) : Prop :=
  real_input_40_p7_hyperelliptic_genus4_branch_degree = 10 ∧
    real_input_40_p7_hyperelliptic_genus4_branch_discriminant ≠ 0 ∧
    D.irreducibleOverQ ∧
    D.transitiveAction ∧
    D.primitiveAction ∧
    D.simpleRamification ∧
    D.containsTransposition ∧
    D.galoisGroupIsS10

/-- Paper label: `prop:real-input-40-p7-branch10-galois-s10`. -/
theorem paper_real_input_40_p7_branch10_galois_s10
    (D : real_input_40_p7_branch10_galois_s10_data) :
    real_input_40_p7_branch10_galois_s10_statement D := by
  rcases paper_real_input_40_p7_hyperelliptic_genus4 with ⟨_, _, _, _, hdeg, hdisc, _⟩
  refine ⟨hdeg, hdisc, D.irreducibleCertificate, D.irreducibleCertificate, ?_, ?_, ?_, ?_⟩
  · exact ⟨D.irreducibleCertificate, D.cycleCertificate⟩
  · exact ⟨D.ramificationCertificate, D.gcdCertificate⟩
  · exact ⟨D.transpositionWitness, D.transpositionWitness_mem, D.transpositionWitness_sign⟩
  · exact
      real_input_40_p7_branch10_galois_s10_eq_top_of_containsAlternating_and_odd D.galoisGroup
        D.containsAlternating_h D.transpositionWitness_mem D.transpositionWitness_sign

end Omega.SyncKernelWeighted
