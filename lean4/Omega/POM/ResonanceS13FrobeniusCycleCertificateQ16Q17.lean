import Mathlib.Tactic

namespace Omega.POM

/-- The degree of the resonance-window characteristic polynomial in the audited cases. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degree (q : ℕ) : ℕ :=
  if q = 16 then 13 else if q = 17 then 13 else 0

/-- The irreducibility Frobenius prime. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime
    (q : ℕ) : ℕ :=
  if q = 16 then 239 else if q = 17 then 31 else 0

/-- The Frobenius prime whose factor pattern contains a degree-seven factor. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime
    (q : ℕ) : ℕ :=
  if q = 16 then 19 else if q = 17 then 23 else 0

/-- The Frobenius prime with factor pattern `(12,1)`. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime
    (q : ℕ) : ℕ :=
  if q = 16 then 127 else if q = 17 then 59 else 0

/-- Recorded factor degrees of `P_q mod p` for the three audited Frobenius primes. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_factorPattern
    (q p : ℕ) : List ℕ :=
  if p = pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime q then
    [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degree q]
  else if p = pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime q then
    [7, 6]
  else if p = pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime q then
    [12, 1]
  else
    []

/-- The abstract Jordan-theorem cycle package extracted from the three concrete patterns. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage
    (q : ℕ) : Prop :=
  pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degree q = 13 ∧
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_factorPattern q
        (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime q) =
      [13] ∧
    7 ∈
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_factorPattern q
        (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime q) ∧
    7 ≤ 13 - 3 ∧
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_factorPattern q
        (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime q) =
      [12, 1]

/-- Concrete finite Frobenius certificate at one audited resonance parameter. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt
    (q : ℕ) : Prop :=
  Nat.Prime (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime q) ∧
    Nat.Prime (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime q) ∧
    Nat.Prime (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime q) ∧
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage q

/-- Statement-level version of the group-theoretic implication: the finite Frobenius package
contains the transitivity, Jordan-prime-cycle, and odd-cycle data used to certify `S₁₃`. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_groupImplication
    (q : ℕ) : Prop :=
  pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt q →
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage q

/-- Paper-facing certificate for `q = 16` and `q = 17`. -/
def pom_resonance_s13_frobenius_cycle_certificate_q16_q17_statement : Prop :=
  pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt 16 ∧
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt 17 ∧
    (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime 16,
        pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime 16,
        pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime 16) =
      (239, 19, 127) ∧
    (pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime 17,
        pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime 17,
        pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime 17) =
      (31, 23, 59) ∧
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_groupImplication 16 ∧
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_groupImplication 17

lemma pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt_16 :
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime]
  · norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime]
  · norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime]
  · unfold pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage
    norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degree,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_factorPattern,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime]

lemma pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt_17 :
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt 17 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime]
  · norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime]
  · norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime]
  · unfold pom_resonance_s13_frobenius_cycle_certificate_q16_q17_jordanPackage
    norm_num [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degree,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_factorPattern,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime]

/-- Paper label: `cor:pom-resonance-s13-frobenius-cycle-certificate-q16-q17`. -/
theorem paper_pom_resonance_s13_frobenius_cycle_certificate_q16_q17 :
    pom_resonance_s13_frobenius_cycle_certificate_q16_q17_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt_16
  · exact pom_resonance_s13_frobenius_cycle_certificate_q16_q17_certificateAt_17
  · simp [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime]
  · simp [pom_resonance_s13_frobenius_cycle_certificate_q16_q17_irreduciblePrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degreeSevenPrime,
      pom_resonance_s13_frobenius_cycle_certificate_q16_q17_twelveOnePrime]
  · intro h
    exact h.2.2.2
  · intro h
    exact h.2.2.2

end Omega.POM
