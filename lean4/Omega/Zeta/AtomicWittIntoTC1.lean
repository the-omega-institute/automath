import Mathlib.RingTheory.MvPolynomial.Basic

namespace Omega.Zeta

universe u v

/-- Chapter-local concrete data for the atomic Big-Witt-to-trace-class compilation. The source
semiring is realized as the free commutative semiring on the atomic generators `(β, n, m)`, while
`block` records the target trace-class block attached to each generator. -/
structure AtomicWittIntoTC1Data where
  Beta : Type u
  TC1 : Type v
  [instCommSemiringTC1 : CommSemiring TC1]
  block : Beta → ℕ → ℕ → TC1

attribute [instance] AtomicWittIntoTC1Data.instCommSemiringTC1

namespace AtomicWittIntoTC1Data

/-- Atomic generators are indexed by the weight `β` together with the multiplicity/period data
`n, m`. -/
def Generator (D : AtomicWittIntoTC1Data) : Type u :=
  D.Beta × ℕ × ℕ

/-- The atomic Big-Witt semiring is modeled as the free commutative semiring on the generators. -/
abbrev WAtom (D : AtomicWittIntoTC1Data) : Type u :=
  MvPolynomial D.Generator ℕ

/-- Distinguished atomic generator. -/
noncomputable def atom (D : AtomicWittIntoTC1Data) (β : D.Beta) (n m : ℕ) : D.WAtom :=
  MvPolynomial.X (β, n, m)

/-- Generator assignment into the trace-class target. -/
def blockOnGenerator (D : AtomicWittIntoTC1Data) : D.Generator → D.TC1
  | ⟨β, n, m⟩ => D.block β n m

/-- Free-semiring extension of the atomic block assignment. -/
noncomputable def lift (D : AtomicWittIntoTC1Data) : D.WAtom →+* D.TC1 :=
  MvPolynomial.eval₂Hom (Nat.castRingHom D.TC1) D.blockOnGenerator

@[simp] theorem lift_atom (D : AtomicWittIntoTC1Data) (β : D.Beta) (n m : ℕ) :
    D.lift (D.atom β n m) = D.block β n m := by
  simp [lift, atom, blockOnGenerator]

end AtomicWittIntoTC1Data

/-- The atomic Big-Witt semiring compiles into the trace-class target by free semiring recursion on
the generators `(β, n, m)`.
    thm:atomic-witt-into-tc1 -/
theorem paper_atomic_witt_into_tc1 (D : AtomicWittIntoTC1Data) :
    ∃ Φ : D.WAtom →+* D.TC1, ∀ β n m, Φ (D.atom β n m) = D.block β n m := by
  refine ⟨D.lift, ?_⟩
  intro β n m
  exact D.lift_atom β n m

end Omega.Zeta
