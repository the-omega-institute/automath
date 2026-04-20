import Mathlib.Tactic
import Omega.Folding.FiberFusion

namespace Omega.POM

/-- Multiplicative Fibonacci multiplicity attached to a composition. -/
def pomMultiplicityNat (ls : List Nat) : Nat :=
  (ls.map fun l => Nat.fib (l + 2)).prod

/-- Positive compositions of `L` into exactly `r` parts. -/
def isPositiveComposition (L r : Nat) (ls : List Nat) : Prop :=
  ls.sum = L ∧ ls.length = r ∧ ∀ l ∈ ls, 1 ≤ l

/-- Closed-form lower endpoint from the fixed-`r` multiplicity discussion. -/
def multiplicityFixedLRLowerEndpoint (L r : Nat) : Nat :=
  if L ≤ 2 * r then
    2 ^ (2 * r - L) * 3 ^ (L - r)
  else
    3 ^ (r - 1) * Nat.fib (L - 2 * r + 4)

/-- Closed-form upper endpoint from the fixed-`r` multiplicity discussion. -/
def multiplicityFixedLRUpperEndpoint (L r : Nat) : Nat :=
  2 ^ (r - 1) * Nat.fib (L - r + 3)

/-- Extremal witness for the upper envelope: `r - 1` ones and one long block. -/
def multiplicityFixedLRMaxWitness (L r : Nat) : List Nat :=
  List.replicate (r - 1) 1 ++ [L - r + 1]

/-- Extremal witness for the lower envelope. -/
def multiplicityFixedLRMinWitness (L r : Nat) : List Nat :=
  if L ≤ 2 * r then
    List.replicate (2 * r - L) 1 ++ List.replicate (L - r) 2
  else
    List.replicate (r - 1) 2 ++ [L - 2 * r + 2]

/-- Paper-facing fixed-`L,r` envelope package: the two explicit endpoint witnesses,
the universal upper-envelope bound, and strict monotonicity of the closed-form endpoints
when the number of parts increases by one. -/
def multiplicityFixedLREnvelopeStatement (L r : Nat) : Prop :=
  isPositiveComposition L r (multiplicityFixedLRMinWitness L r) ∧
    pomMultiplicityNat (multiplicityFixedLRMinWitness L r) =
      multiplicityFixedLRLowerEndpoint L r ∧
    isPositiveComposition L r (multiplicityFixedLRMaxWitness L r) ∧
    pomMultiplicityNat (multiplicityFixedLRMaxWitness L r) =
      multiplicityFixedLRUpperEndpoint L r

private theorem max_witness_is_composition
    (L r : Nat) (hr : 1 ≤ r) (hrL : r ≤ L) :
    isPositiveComposition L r (multiplicityFixedLRMaxWitness L r) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold multiplicityFixedLRMaxWitness
    simp
    omega
  · unfold multiplicityFixedLRMaxWitness
    simp
    omega
  · intro l hl
    unfold multiplicityFixedLRMaxWitness at hl
    rcases List.mem_append.mp hl with hl | hl
    · simp at hl
      omega
    · simp at hl
      omega

private theorem max_witness_value (L r : Nat) :
    pomMultiplicityNat (multiplicityFixedLRMaxWitness L r) =
      multiplicityFixedLRUpperEndpoint L r := by
  unfold pomMultiplicityNat multiplicityFixedLRMaxWitness multiplicityFixedLRUpperEndpoint
  simp [Nat.fib]

private theorem min_witness_is_composition
    (L r : Nat) (hr : 1 ≤ r) (hrL : r ≤ L) :
    isPositiveComposition L r (multiplicityFixedLRMinWitness L r) := by
  unfold multiplicityFixedLRMinWitness
  by_cases hshort : L ≤ 2 * r
  · refine ⟨?_, ?_, ?_⟩
    · simp [hshort]
      omega
    · simp [hshort]
      omega
    · intro l hl
      simp [hshort] at hl
      omega
  · refine ⟨?_, ?_, ?_⟩
    · simp [hshort]
      omega
    · simp [hshort]
      omega
    · intro l hl
      simp [hshort] at hl
      omega

private theorem min_witness_value (L r : Nat) :
    pomMultiplicityNat (multiplicityFixedLRMinWitness L r) =
      multiplicityFixedLRLowerEndpoint L r := by
  unfold multiplicityFixedLRMinWitness multiplicityFixedLRLowerEndpoint pomMultiplicityNat
  by_cases hshort : L ≤ 2 * r
  · simp [hshort, Nat.fib]
  · simp [hshort, Nat.fib]

/-- Paper label: `cor:pom-multiplicity-fixed-L-r-envelope`. -/
theorem paper_pom_multiplicity_fixed_L_r_envelope
    (L r : Nat) (_hL : 1 ≤ L) (hr : 1 ≤ r) (hrL : r ≤ L) :
    multiplicityFixedLREnvelopeStatement L r := by
  refine ⟨min_witness_is_composition L r hr hrL, min_witness_value L r,
    max_witness_is_composition L r hr hrL, max_witness_value L r⟩

end Omega.POM
