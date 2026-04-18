import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Multiplication by every prime is bijective on the additive group. -/
def PrimeMultiplicationBijective (V : Type*) [AddCommGroup V] : Prop :=
  ∀ p, Nat.Prime p → Function.Bijective fun v : V => p • v

/-- Prime-by-prime divisibility on the additive group. -/
def PrimeDivisible (V : Type*) [AddCommGroup V] : Prop :=
  ∀ p, Nat.Prime p → ∀ v : V, ∃ w : V, p • w = v

/-- A concrete torsion-freeness predicate for the additive group. -/
def AdditiveTorsionFree (V : Type*) [AddCommGroup V] : Prop :=
  ∀ n : ℕ, ∀ v : V, n • v = 0 → n = 0 ∨ v = 0

/-- Paper-facing alias for the dual universal-solenoid conclusion. -/
def UniversalSolenoidDualQConclusion (V : Type*) [AddCommGroup V] [Module ℚ V] : Prop :=
  Nonempty (V ≃ₗ[ℚ] ℚ)

/-- Prime-by-prime divisibility plus rank one forces the discrete dual model to be `ℚ`; the rank
condition is recorded both as `circleDim 1 0 = 1` and as a one-dimensional `ℚ`-vector-space
equivalence.
    thm:cdim-cdim1-divisible-implies-Q -/
theorem paper_cdim_cdim1_divisible_implies_q
    (V : Type*) [AddCommGroup V] [Module ℚ V] [Module.Free ℚ V] [Module.Finite ℚ V]
    (hprime : PrimeMultiplicationBijective V) (hrank : Module.finrank ℚ V = 1) :
    PrimeDivisible V ∧ AdditiveTorsionFree V ∧ circleDim 1 0 = 1 ∧
      UniversalSolenoidDualQConclusion V := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp v
    exact (hprime p hp).2 v
  · intro n v hv
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      have hnq : (n : ℚ) ≠ 0 := by
        exact_mod_cast hn
      have hvq : (n : ℚ) • v = 0 := by
        rw [Nat.cast_smul_eq_nsmul ℚ n]
        exact hv
      have hmul := congrArg (fun x : V => ((n : ℚ)⁻¹) • x) hvq
      simpa [smul_smul, hnq] using hmul
  · simp [circleDim]
  · have hfin : Module.finrank ℚ V = Module.finrank ℚ ℚ := by
      calc
        Module.finrank ℚ V = 1 := hrank
        _ = Module.finrank ℚ ℚ := by simp
    exact ⟨LinearEquiv.ofFinrankEq V ℚ hfin⟩

end Omega.CircleDimension
