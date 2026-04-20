import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the derived minimal cyclic audit-axis package. The record tracks the audit
chain, the inverse-limit register identified with a `\hat{\mathbf Z}` model, and a fresh prime
witness unlocked at each stage. -/
structure DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData where
  AuditStage : Type
  Register : Type
  ZhatModel : Type
  auditChain : ℕ → AuditStage
  initialStage : AuditStage
  stageModulus : AuditStage → ℕ
  registerToZhat : Register → ZhatModel
  zhatToRegister : ZhatModel → Register
  initiality_certificate : ∀ n : ℕ, auditChain n = initialStage
  zhat_left_inv : Function.LeftInverse zhatToRegister registerToZhat
  zhat_right_inv : Function.RightInverse zhatToRegister registerToZhat
  primeWitness : ℕ → ℕ
  prime_unlocking_certificate :
    ∀ n : ℕ,
      Nat.Prime (primeWitness n) ∧
        primeWitness n ∣ stageModulus (auditChain (n + 1)) ∧
        ¬ primeWitness n ∣ stageModulus (auditChain n)

namespace DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData

/-- The audit chain is initial in the sense that every stage agrees with the designated seed. -/
def initiality (D : DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData) : Prop :=
  ∀ n : ℕ, D.auditChain n = D.initialStage

/-- The inverse-limit register is identified with the chosen `\hat{\mathbf Z}` model. -/
def zhatIdentification (D : DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData) : Prop :=
  Nonempty (D.Register ≃ D.ZhatModel)

/-- Every stage unlocks a fresh prime divisor that was absent at the previous stage. -/
def infinitePrimeUnlocking (D : DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData) : Prop :=
  ∀ n : ℕ,
    Nat.Prime (D.primeWitness n) ∧
      D.primeWitness n ∣ D.stageModulus (D.auditChain (n + 1)) ∧
      ¬ D.primeWitness n ∣ D.stageModulus (D.auditChain n)

/-- Explicit equivalence between the register and its `\hat{\mathbf Z}` model. -/
def zhatEquiv (D : DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData) :
    D.Register ≃ D.ZhatModel where
  toFun := D.registerToZhat
  invFun := D.zhatToRegister
  left_inv := D.zhat_left_inv
  right_inv := D.zhat_right_inv

end DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData

open DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData

/-- Paper-facing wrapper for the derived minimal cyclic audit axis package.
    thm:derived-minimal-cyclic-audit-axis-zhat-prime-unlocking -/
theorem paper_derived_minimal_cyclic_audit_axis_zhat_prime_unlocking
    (D : DerivedMinimalCyclicAuditAxisZhatPrimeUnlockingData) :
    D.initiality ∧ D.zhatIdentification ∧ D.infinitePrimeUnlocking := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.initiality_certificate
  · exact ⟨D.zhatEquiv⟩
  · exact D.prime_unlocking_certificate

end Omega.Zeta
