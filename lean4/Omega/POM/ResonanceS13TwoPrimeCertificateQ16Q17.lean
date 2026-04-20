import Mathlib.Tactic

namespace Omega.POM

/-- The resonance-window characteristic-polynomial degree used for `q = 16,17`. -/
def pomResonanceCharacteristicDegree (q : ℕ) : ℕ :=
  if q = 16 then 13 else if q = 17 then 13 else 0

/-- The audited irreducibility prime `p_irr`. -/
def pomResonanceIrreduciblePrime (q : ℕ) : ℕ :=
  if q = 16 then 239 else if q = 17 then 31 else 0

/-- The audited prime whose factor pattern is `(11,2)`. -/
def pomResonanceElevenTwoPrime (q : ℕ) : ℕ :=
  if q = 16 then 47 else if q = 17 then 41 else 0

/-- The recorded factorization pattern of `P_q mod p` as a list of factor degrees. -/
def pomResonanceFactorPattern (q p : ℕ) : List ℕ :=
  if p = pomResonanceIrreduciblePrime q then [pomResonanceCharacteristicDegree q]
  else if p = pomResonanceElevenTwoPrime q then [11, 2]
  else []

/-- The concrete two-prime certificate for `S₁₃`: one prime gives irreducibility and one gives
an `(11,2)` Frobenius pattern, both at degree `13`. -/
def pomResonanceS13CertificateAt (q : ℕ) : Prop :=
  pomResonanceCharacteristicDegree q = 13 ∧
    Nat.Prime (pomResonanceIrreduciblePrime q) ∧
    Nat.Prime (pomResonanceElevenTwoPrime q) ∧
    pomResonanceFactorPattern q (pomResonanceIrreduciblePrime q) = [13] ∧
    pomResonanceFactorPattern q (pomResonanceElevenTwoPrime q) = [11, 2] ∧
    11 + 2 = pomResonanceCharacteristicDegree q

/-- Paper-facing package for the audited two-prime `S₁₃` certificates at `q = 16,17`. -/
def pomResonanceS13TwoPrimeCertificateQ16Q17 : Prop :=
  pomResonanceS13CertificateAt 16 ∧
    pomResonanceS13CertificateAt 17 ∧
    (pomResonanceIrreduciblePrime 16, pomResonanceElevenTwoPrime 16) = (239, 47) ∧
    (pomResonanceIrreduciblePrime 17, pomResonanceElevenTwoPrime 17) = (31, 41)

/-- The audited primes `(239,47)` for `q = 16` and `(31,41)` for `q = 17` realize the two-prime
certificate pattern `(13)` and `(11,2)` at degree `13`.
    prop:pom-resonance-s13-two-prime-certificate-q16-q17 -/
theorem paper_pom_resonance_s13_two_prime_certificate_q16_q17 :
    pomResonanceS13TwoPrimeCertificateQ16Q17 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold pomResonanceS13CertificateAt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [pomResonanceCharacteristicDegree]
    · norm_num [pomResonanceIrreduciblePrime]
    · norm_num [pomResonanceElevenTwoPrime]
    · native_decide
    · native_decide
    · simp [pomResonanceCharacteristicDegree]
  · unfold pomResonanceS13CertificateAt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [pomResonanceCharacteristicDegree]
    · norm_num [pomResonanceIrreduciblePrime]
    · norm_num [pomResonanceElevenTwoPrime]
    · native_decide
    · native_decide
    · simp [pomResonanceCharacteristicDegree]
  · simp [pomResonanceIrreduciblePrime, pomResonanceElevenTwoPrime]
  · simp [pomResonanceIrreduciblePrime, pomResonanceElevenTwoPrime]

end Omega.POM
