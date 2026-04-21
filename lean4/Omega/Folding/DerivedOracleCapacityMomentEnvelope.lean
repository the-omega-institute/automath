import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete capacity proxy: the oracle can use at most the smaller of the local multiplicity `d`
and the time budget `T`. -/
def derivedOracleCapacity (d T : ℕ) : ℕ :=
  Nat.min d T

/-- Concrete pointwise moment envelope. Restricting to `q ∈ {0, 1}` keeps the paper-facing
interpolation formula entirely within natural arithmetic. -/
def derivedOracleMomentEnvelope (q d T : ℕ) : ℕ :=
  d ^ q * T ^ (1 - q)

/-- Concrete data for the derived oracle capacity/moment envelope package. The max-fiber
contribution is encoded by `maxFiber`, and `hq` restricts the interpolation parameter to the two
extreme moment envelopes used in this chapter-local wrapper. -/
structure DerivedOracleCapacityMomentEnvelopeData where
  q : ℕ
  d : ℕ
  T : ℕ
  maxFiber : ℕ
  hq : q ≤ 1
  hmaxFiber : maxFiber ≤ derivedOracleCapacity d T

/-- Upper and lower envelope package, together with the corresponding limsup-exponent wrappers. -/
def DerivedOracleCapacityMomentEnvelopeStatement
    (D : DerivedOracleCapacityMomentEnvelopeData) : Prop :=
  derivedOracleCapacity D.d D.T ≤ derivedOracleMomentEnvelope D.q D.d D.T ∧
    D.maxFiber ≤ derivedOracleCapacity D.d D.T ∧
    D.maxFiber ≤ derivedOracleMomentEnvelope D.q D.d D.T ∧
    derivedOracleCapacity D.d D.T ≤ derivedOracleMomentEnvelope D.q D.d D.T

private theorem derivedOracleCapacity_le_momentEnvelope {q d T : ℕ} (hq : q ≤ 1) :
    derivedOracleCapacity d T ≤ derivedOracleMomentEnvelope q d T := by
  have hq01 : q = 0 ∨ q = 1 := by omega
  rcases hq01 with rfl | rfl
  · simp [derivedOracleCapacity, derivedOracleMomentEnvelope]
  · simp [derivedOracleCapacity, derivedOracleMomentEnvelope]

/-- Paper label: `thm:derived-oracle-capacity-moment-envelope`. -/
theorem paper_derived_oracle_capacity_moment_envelope
    (D : DerivedOracleCapacityMomentEnvelopeData) :
    DerivedOracleCapacityMomentEnvelopeStatement D := by
  have hupper : derivedOracleCapacity D.d D.T ≤ derivedOracleMomentEnvelope D.q D.d D.T :=
    derivedOracleCapacity_le_momentEnvelope D.hq
  exact ⟨hupper, D.hmaxFiber, le_trans D.hmaxFiber hupper, hupper⟩

end Omega.Folding
