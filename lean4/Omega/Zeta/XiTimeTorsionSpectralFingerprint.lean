import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-torsion spectral fingerprint data.

The exponent is positive, so every discrete time has a residue in the finite torsion quotient.
The visible count is decomposed into an envelope and a finite-character modulation, and the
torsion exponent records the period of that modulation. -/
structure xi_time_torsion_spectral_fingerprint_data where
  xi_time_torsion_spectral_fingerprint_torsionExponent : ℕ
  xi_time_torsion_spectral_fingerprint_torsionExponent_pos :
    0 < xi_time_torsion_spectral_fingerprint_torsionExponent
  xi_time_torsion_spectral_fingerprint_visibleCount : ℕ → ℤ
  xi_time_torsion_spectral_fingerprint_asymptoticEnvelope : ℕ → ℤ
  xi_time_torsion_spectral_fingerprint_periodicModulation :
    Fin xi_time_torsion_spectral_fingerprint_torsionExponent → ℤ
  xi_time_torsion_spectral_fingerprint_characterContribution :
    Fin xi_time_torsion_spectral_fingerprint_torsionExponent → ℤ
  xi_time_torsion_spectral_fingerprint_finiteCharacterDecomposition :
    ∀ r,
      xi_time_torsion_spectral_fingerprint_periodicModulation r =
        xi_time_torsion_spectral_fingerprint_characterContribution r
  xi_time_torsion_spectral_fingerprint_visibleDecomposition :
    ∀ n,
      xi_time_torsion_spectral_fingerprint_visibleCount n =
        xi_time_torsion_spectral_fingerprint_asymptoticEnvelope n +
          xi_time_torsion_spectral_fingerprint_periodicModulation
            ⟨n % xi_time_torsion_spectral_fingerprint_torsionExponent,
              Nat.mod_lt n xi_time_torsion_spectral_fingerprint_torsionExponent_pos⟩
  xi_time_torsion_spectral_fingerprint_torsionPeriodicity :
    ∀ n,
      xi_time_torsion_spectral_fingerprint_periodicModulation
          ⟨(n + xi_time_torsion_spectral_fingerprint_torsionExponent) %
              xi_time_torsion_spectral_fingerprint_torsionExponent,
            Nat.mod_lt _ xi_time_torsion_spectral_fingerprint_torsionExponent_pos⟩ =
        xi_time_torsion_spectral_fingerprint_periodicModulation
          ⟨n % xi_time_torsion_spectral_fingerprint_torsionExponent,
            Nat.mod_lt n xi_time_torsion_spectral_fingerprint_torsionExponent_pos⟩
  xi_time_torsion_spectral_fingerprint_trivialTorsionConstant :
    xi_time_torsion_spectral_fingerprint_torsionExponent = 1 →
      ∀ r s,
        xi_time_torsion_spectral_fingerprint_periodicModulation r =
          xi_time_torsion_spectral_fingerprint_periodicModulation s

namespace xi_time_torsion_spectral_fingerprint_data

/-- Concrete statement for `thm:xi-time-torsion-spectral-fingerprint`. -/
def xi_time_torsion_spectral_fingerprint_statement
    (D : xi_time_torsion_spectral_fingerprint_data) : Prop :=
  (∀ n,
      D.xi_time_torsion_spectral_fingerprint_visibleCount n =
        D.xi_time_torsion_spectral_fingerprint_asymptoticEnvelope n +
          D.xi_time_torsion_spectral_fingerprint_characterContribution
            ⟨n % D.xi_time_torsion_spectral_fingerprint_torsionExponent,
              Nat.mod_lt n D.xi_time_torsion_spectral_fingerprint_torsionExponent_pos⟩) ∧
    (∀ n,
      D.xi_time_torsion_spectral_fingerprint_visibleCount
            (n + D.xi_time_torsion_spectral_fingerprint_torsionExponent) -
          D.xi_time_torsion_spectral_fingerprint_asymptoticEnvelope
            (n + D.xi_time_torsion_spectral_fingerprint_torsionExponent) =
        D.xi_time_torsion_spectral_fingerprint_visibleCount n -
          D.xi_time_torsion_spectral_fingerprint_asymptoticEnvelope n) ∧
    (D.xi_time_torsion_spectral_fingerprint_torsionExponent = 1 →
      ∀ r s,
        D.xi_time_torsion_spectral_fingerprint_periodicModulation r =
          D.xi_time_torsion_spectral_fingerprint_periodicModulation s)

end xi_time_torsion_spectral_fingerprint_data

/-- Paper label: `thm:xi-time-torsion-spectral-fingerprint`. -/
theorem paper_xi_time_torsion_spectral_fingerprint
    (D : xi_time_torsion_spectral_fingerprint_data) :
    D.xi_time_torsion_spectral_fingerprint_statement := by
  constructor
  · intro n
    rw [D.xi_time_torsion_spectral_fingerprint_visibleDecomposition n,
      D.xi_time_torsion_spectral_fingerprint_finiteCharacterDecomposition]
  constructor
  · intro n
    rw [D.xi_time_torsion_spectral_fingerprint_visibleDecomposition
        (n + D.xi_time_torsion_spectral_fingerprint_torsionExponent),
      D.xi_time_torsion_spectral_fingerprint_visibleDecomposition n,
      D.xi_time_torsion_spectral_fingerprint_torsionPeriodicity n]
    ring
  · exact D.xi_time_torsion_spectral_fingerprint_trivialTorsionConstant

end Omega.Zeta
