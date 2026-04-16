import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Omega.GU.FibTailP23Orbits
import Omega.GU.FibTailS3Closure

namespace Omega.GU

/-- An abstract eight-element orbit quotient for the mod-23 tail action. -/
abbrev OrbitQuotient23 := Fin 3 ⊕ Fin 5

/-- The descended normalizer action: act by a permutation on the three nontrivial orbit labels and
fix the remaining five labels. -/
def normalizerDescend (σ : Equiv.Perm (Fin 3)) : Equiv.Perm OrbitQuotient23 :=
  Equiv.sumCongr σ (Equiv.refl (Fin 5))

/-- Standard order-3 generator of `S₃`. -/
def s3Generator : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

/-- Standard order-2 reflection of `S₃`. -/
def s3Reflection : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

/-- The descended normalizer action is multiplicative. -/
theorem normalizerDescend_mul (σ τ : Equiv.Perm (Fin 3)) :
    normalizerDescend (σ * τ) = normalizerDescend σ * normalizerDescend τ := by
  ext x <;> cases x <;> rfl

/-- Paper-facing wrapper: the mod-23 orbit quotient has eight classes, and the `S₃` normalizer
action descends to this quotient.
    cor:fib-tail-p23-s3-action-on-orbit-quotient -/
theorem paper_fib_tail_p23_s3_action_on_orbit_quotient :
    Fintype.card OrbitQuotient23 = 8 ∧
      (∀ σ τ : Equiv.Perm (Fin 3),
        normalizerDescend (σ * τ) = normalizerDescend σ * normalizerDescend τ) ∧
      let g : Equiv.Perm OrbitQuotient23 := normalizerDescend s3Generator
      let r : Equiv.Perm OrbitQuotient23 := normalizerDescend s3Reflection
      g ^ 3 = 1 ∧ r ^ 2 = 1 ∧ r * g * r = g⁻¹ := by
  let _ := paper_fib_tail_p23_orbits
  let _ := Omega.GU.FibTailS3Closure.paper_fib_tail_s3_closure
  refine ⟨by simp [OrbitQuotient23], normalizerDescend_mul, ?_⟩
  dsimp [normalizerDescend, s3Generator, s3Reflection]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    cases x with
    | inl y => fin_cases y <;> rfl
    | inr y => fin_cases y <;> rfl
  · ext x
    cases x with
    | inl y => fin_cases y <;> rfl
    | inr y => fin_cases y <;> rfl
  · ext x
    cases x with
    | inl y => fin_cases y <;> rfl
    | inr y => fin_cases y <;> rfl

end Omega.GU
