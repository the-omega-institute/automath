import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The chapter-local proxy pair `(χ, u)` used for the renormalization gate. -/
abbrev WittDirichletPair := (ℕ → ℚ) × (ℕ → ℚ)

/-- Simultaneous substitution `n ↦ d * n` on both coordinates. -/
def renormGate (d : Nat) (D : WittDirichletPair) : WittDirichletPair :=
  (fun n => D.1 (d * n), fun n => D.2 (d * n))

/-- The same substitution acting on a single sequence. -/
def renormSequence (d : Nat) (f : ℕ → ℚ) : ℕ → ℚ :=
  fun n => f (d * n)

/-- A lightweight twisted Witt-Mobius proxy: both coordinates are substituted simultaneously. -/
def twistedWittMobius (D : WittDirichletPair) : ℕ → ℚ :=
  fun n => D.1 n - D.2 n

/-- A lightweight Euler-product proxy for the same pair. -/
def twistedEulerProduct (D : WittDirichletPair) : ℕ → ℚ :=
  fun n => D.1 n * D.2 n

/-- Composition of renormalization gates multiplies the scales. -/
def renormSemigroupLaw (d e : Nat) (D : WittDirichletPair) : Prop :=
  renormGate d (renormGate e D) = renormGate (d * e) D

/-- The twisted Witt-Mobius and Euler-product readouts commute with simultaneous substitution. -/
def renormTwistCompatibility (d : Nat) (D : WittDirichletPair) : Prop :=
  twistedWittMobius (renormGate d D) = renormSequence d (twistedWittMobius D) ∧
    twistedEulerProduct (renormGate d D) = renormSequence d (twistedEulerProduct D)

/-- Paper label: `prop:witt-renorm-monoid`. -/
theorem paper_witt_renorm_monoid (d e : Nat) (χ u : ℕ → ℚ) :
    renormSemigroupLaw d e (χ, u) ∧
      renormTwistCompatibility d (χ, u) := by
  constructor
  · ext n <;> simp [renormGate, Nat.mul_left_comm, Nat.mul_comm]
  · constructor <;> ext n <;> rfl

end Omega.SyncKernelWeighted
