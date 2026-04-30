import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete dyadic-Fibonacci completion package.  The equivalence with `ℕ` records that the
dyadic prime coordinates are countably infinite. -/
structure xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data where
  PrimeIndex : Type
  primeIndexDecidableEq : DecidableEq PrimeIndex
  primeEnumeration : ℕ ≃ PrimeIndex

namespace xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data

/-- Idempotents in the split product are coordinatewise Boolean choices. -/
abbrev idempotentSkeleton
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) :=
  D.PrimeIndex → Bool

/-- The Boolean idempotent skeleton is the standard Cantor cube over countably many coordinates. -/
def idempotentSkeletonCantor
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) : Prop :=
  Nonempty (D.idempotentSkeleton ≃ (ℕ → Bool))

/-- There is an injection from the binary sequence space into idempotents. -/
def continuumManyIdempotents
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) : Prop :=
  ∃ encode : (ℕ → Bool) → D.idempotentSkeleton, Function.Injective encode

/-- Arbitrarily many distinct coordinate maximal ideals are witnessed by finite initial prime
segments. -/
def notSemilocal
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) : Prop :=
  ∀ n : ℕ, ∃ axes : Fin n → D.PrimeIndex, Function.Injective axes

/-- Boolean idempotents supported on the first `n` dyadic prime coordinates. -/
def supportedOnFirst
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) (n : ℕ) :
    Set D.idempotentSkeleton :=
  {e | ∀ p, p ∉ Set.range (fun i : Fin n => D.primeEnumeration i.val) → e p = false}

/-- The finite-support ideals form a strictly ascending chain. -/
def notNoetherian
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) : Prop :=
  ∀ n : ℕ, D.supportedOnFirst n ⊂ D.supportedOnFirst (n + 1)

end xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data

/-- Paper label: `cor:xi-dyadic-fibonacci-completion-cantor-idempotent-skeleton`. -/
theorem paper_xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton
    (D : xi_dyadic_fibonacci_completion_cantor_idempotent_skeleton_Data) :
    D.idempotentSkeletonCantor ∧ D.continuumManyIdempotents ∧ D.notSemilocal ∧
      D.notNoetherian := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?cantorEquiv⟩
    exact
      { toFun := fun e n => e (D.primeEnumeration n)
        invFun := fun a p => a (D.primeEnumeration.symm p)
        left_inv := by
          intro e
          funext p
          simp
        right_inv := by
          intro a
          funext n
          simp }
  · refine ⟨fun a p => a (D.primeEnumeration.symm p), ?_⟩
    intro a b h
    funext n
    have hpoint := congr_fun h (D.primeEnumeration n)
    simpa using hpoint
  · intro n
    refine ⟨fun i : Fin n => D.primeEnumeration i.val, ?_⟩
    intro i j hij
    apply Fin.ext
    exact D.primeEnumeration.injective hij
  · intro n
    constructor
    · intro e he p hp
      apply he p
      intro hpFirst
      apply hp
      rcases hpFirst with ⟨i, rfl⟩
      exact ⟨⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩, rfl⟩
    · intro hreverse
      let fresh : D.idempotentSkeleton :=
        fun p => if p = D.primeEnumeration n then true else false
      have hfresh_succ : fresh ∈ D.supportedOnFirst (n + 1) := by
        intro p hp
        by_cases hpeq : p = D.primeEnumeration n
        · exfalso
          apply hp
          exact ⟨⟨n, Nat.lt_succ_self n⟩, by simp [hpeq]⟩
        · simp [fresh, hpeq]
      have hfresh_first : fresh ∈ D.supportedOnFirst n := hreverse hfresh_succ
      have hnot_mem :
          D.primeEnumeration n ∉ Set.range (fun i : Fin n => D.primeEnumeration i.val) := by
        rintro ⟨i, hi⟩
        have hn_eq : n = i.val := D.primeEnumeration.injective hi.symm
        exact Nat.ne_of_gt i.isLt hn_eq
      have hfalse := hfresh_first (D.primeEnumeration n) hnot_mem
      simp [fresh] at hfalse

end Omega.Zeta
