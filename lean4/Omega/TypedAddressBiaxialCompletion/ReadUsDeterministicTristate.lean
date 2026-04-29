import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ReadUsTypedPrecision


namespace Omega.TypedAddressBiaxialCompletion

/-- Reproducibility across implementations means that matching verifier semantics and matching
certificate backends force the same typed `Read_US` output. -/
def reproducibleAcrossImplementations (a : AddrUS) (Ver₁ Ver₂ : TypedCertificate → Bool)
    (cert₁? cert₂? : Option TypedCertificate) : Prop :=
  Read_US a Ver₁ cert₁? = Read_US a Ver₂ cert₂?

/-- `NULL` has structural meaning exactly when it records the absence of any acceptable typed
certificate, either because no certificate is present or because the available one is ill-typed or
rejected by the verifier. -/
def nullHasStructuralMeaning (a : AddrUS) (Ver : TypedCertificate → Bool)
    (cert? : Option TypedCertificate) : Prop :=
  Read_US a Ver cert? = ReadUSOutput.NULL ↔
    cert? = none ∨
      ∃ cert, cert? = some cert ∧
        (precisionCompatible a cert = false ∨ Ver cert = false)

/-- Paper label: `thm:xi-us-deterministic-tristate`. The typed-address `Read_US` backend is
deterministic once the verifier semantics and the optional typed certificate are fixed, and its
`NULL` branch is exactly the structural failure of typed certificate production. -/
theorem paper_xi_us_deterministic_tristate
    (a : AddrUS) (Ver₁ Ver₂ : TypedCertificate → Bool)
    (cert₁? cert₂? : Option TypedCertificate)
    (hVer : ∀ cert, Ver₁ cert = Ver₂ cert) (hcert : cert₁? = cert₂?) :
    reproducibleAcrossImplementations a Ver₁ Ver₂ cert₁? cert₂? ∧
      nullHasStructuralMeaning a Ver₁ cert₁? := by
  constructor
  · cases hcert
    cases cert₁? with
    | none =>
        simp [reproducibleAcrossImplementations, Read_US]
    | some cert =>
        have hV : Ver₁ cert = Ver₂ cert := hVer cert
        by_cases hTyped : precisionCompatible a cert = true
        · by_cases hPass : Ver₁ cert = true
          · have hPass₂ : Ver₂ cert = true := by
              simpa [hV] using hPass
            cases hVerdict : cert.verdict <;>
              simp [reproducibleAcrossImplementations, Read_US, hTyped, hPass, hPass₂, hVerdict]
          · have hFail₁ : Ver₁ cert = false := by
              cases hEval : Ver₁ cert <;> simp [hEval] at hPass ⊢
            have hFail₂ : Ver₂ cert = false := by
              simpa [hV] using hFail₁
            simp [reproducibleAcrossImplementations, Read_US, hTyped, hFail₁, hFail₂]
        · simp [reproducibleAcrossImplementations, Read_US, hTyped]
  · cases cert₁? with
    | none =>
        simp [nullHasStructuralMeaning, Read_US]
    | some cert =>
        by_cases hTyped : precisionCompatible a cert = true
        · by_cases hPass : Ver₁ cert = true
          · cases hVerdict : cert.verdict <;>
              simp [nullHasStructuralMeaning, Read_US, hTyped, hPass, hVerdict]
          · simp [nullHasStructuralMeaning, Read_US, hTyped, hPass]
        · simp [nullHasStructuralMeaning, Read_US, hTyped]

end Omega.TypedAddressBiaxialCompletion
