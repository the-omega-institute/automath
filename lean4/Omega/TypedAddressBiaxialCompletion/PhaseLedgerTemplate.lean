import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

namespace Omega.TypedAddressBiaxialCompletion

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Minimal chapter-local template for the phase/ledger splitting pattern used in the typed-address
chapter. It records the connected phase side, the totally disconnected ledger side, short exact
extension data, a compatible prefix readout, and a distinguished localized prime. -/
structure PhaseLedgerTemplate where
  phaseCarrier : Type
  ledgerCarrier : Type
  extensionCarrier : Type
  prefixDepth : Nat
  continuousPhaseStatement : Prop
  continuousPhaseWitness : continuousPhaseStatement
  totallyDisconnectedLedgerStatement : Prop
  totallyDisconnectedLedgerWitness : totallyDisconnectedLedgerStatement
  shortExactExtensionStatement : Prop
  shortExactExtensionWitness : shortExactExtensionStatement
  compatiblePrefixReadoutStatement : Prop
  compatiblePrefixReadoutWitness : compatiblePrefixReadoutStatement
  localizedPrime : ℕ
  localizedPrime_isPrime : Nat.Prime localizedPrime
  phaseRank : Nat
  phaseRank_one : phaseRank = 1

/-- The template has a continuous phase factor exactly when its connected phase witness is present. -/
def PhaseLedgerTemplate.hasContinuousPhaseFactor (T : PhaseLedgerTemplate) : Prop :=
  T.continuousPhaseStatement

/-- The template has a totally disconnected ledger factor exactly when its ledger witness is
present. -/
def PhaseLedgerTemplate.hasTotallyDisconnectedLedgerFactor (T : PhaseLedgerTemplate) : Prop :=
  T.totallyDisconnectedLedgerStatement

/-- A rank-one prime-localized model packages the local prime witness together with the short exact
extension, prefix compatibility, and the rank-one half-circle-dimension normalization. -/
def PhaseLedgerTemplate.hasPrimeLocalizedModel (T : PhaseLedgerTemplate) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ T.shortExactExtensionStatement ∧ T.compatiblePrefixReadoutStatement ∧
    T.phaseRank = 1 ∧ implHalfCircleDim = (1 : ℚ) / 2

private theorem rankOne_prime_localized_half_circle :
    implHalfCircleDim = (1 : ℚ) / 2 := by
  simpa using (paper_xi_finite_prime_support_multiplicative_half_circle_dimension 1).2.1

/-- The localized rank-one model attached to a phase/ledger template is obtained by combining the
template witnesses with the existing rank-one prime-support half-circle-dimension split.
    prop:typed-address-biaxial-completion-phase-ledger-template -/
theorem paper_typed_address_biaxial_completion_phase_ledger_template (T : PhaseLedgerTemplate) :
    T.hasContinuousPhaseFactor ∧ T.hasTotallyDisconnectedLedgerFactor ∧ T.hasPrimeLocalizedModel :=
    by
  refine ⟨T.continuousPhaseWitness, T.totallyDisconnectedLedgerWitness, ?_⟩
  refine ⟨T.localizedPrime, T.localizedPrime_isPrime, T.shortExactExtensionWitness,
    T.compatiblePrefixReadoutWitness, T.phaseRank_one, rankOne_prime_localized_half_circle⟩

end Omega.TypedAddressBiaxialCompletion
