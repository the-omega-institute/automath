import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Omega.GroupUnification.GroupJGPrimeRegisterInitialObject

namespace Omega.GroupUnification

/-- Concrete states in the chapter-local fold model: a base point, the odd-parity hidden bit,
and a finite set of admissible fiber choices. -/
structure FoldOmega (m : ℕ) where
  base : Fin (m + 1)
  hidden : Bool
  choices : Finset (Fin m)

/-- The `v`-th prime used to externalize a fiber choice. -/
noncomputable def foldPrime {m : ℕ} (v : Fin m) : ℕ :=
  Nat.nth Nat.Prime v

theorem foldPrime_prime {m : ℕ} (v : Fin m) : Nat.Prime (foldPrime v) := by
  simpa [foldPrime] using Nat.prime_nth_prime (v : ℕ)

theorem foldPrime_injective {m : ℕ} : Function.Injective (@foldPrime m) := by
  intro v w h
  apply Fin.ext
  exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h

/-- Squarefree product code for a finite fiber choice. -/
noncomputable def foldSquarefreeCode {m : ℕ} (S : Finset (Fin m)) : ℕ :=
  ∏ v ∈ S, foldPrime v

theorem foldPrime_dvd_squarefreeCode_iff {m : ℕ} (S : Finset (Fin m)) (v : Fin m) :
    foldPrime v ∣ foldSquarefreeCode S ↔ v ∈ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hnot : ¬ foldPrime v ∣ 1 := (foldPrime_prime v).not_dvd_one
      simp [foldSquarefreeCode, hnot]
  | @insert a S ha ih =>
      have hEq : foldPrime v ∣ foldPrime a ↔ v = a := by
        constructor
        · intro hdiv
          apply foldPrime_injective
          exact (Nat.prime_dvd_prime_iff_eq (foldPrime_prime v) (foldPrime_prime a)).1 hdiv
        · intro hEq'
          subst hEq'
          exact dvd_rfl
      rw [foldSquarefreeCode, Finset.prod_insert ha, Nat.Prime.dvd_mul (foldPrime_prime v), hEq]
      simpa [Finset.mem_insert] using (or_congr Iff.rfl ih)

theorem foldSquarefreeCode_injective {m : ℕ} :
    Function.Injective (@foldSquarefreeCode m) := by
  intro S T hST
  apply Finset.ext
  intro v
  rw [← foldPrime_dvd_squarefreeCode_iff S v, hST, foldPrime_dvd_squarefreeCode_iff T v]

/-- The explicit squarefree externalization map. -/
noncomputable def foldPsi (m : ℕ) : FoldOmega m → Fin (m + 1) × Bool × ℕ
  | ω => (ω.base, ω.hidden, foldSquarefreeCode ω.choices)

theorem foldPsi_injective (m : ℕ) : Function.Injective (foldPsi m) := by
  intro ω ω' h
  rcases ω with ⟨base, hidden, choices⟩
  rcases ω' with ⟨base', hidden', choices'⟩
  have hBase : base = base' := by
    simpa [foldPsi] using congrArg Prod.fst h
  have hTail :
      (hidden, foldSquarefreeCode choices) = (hidden', foldSquarefreeCode choices') := by
    simpa [foldPsi, hBase] using congrArg Prod.snd h
  have hHidden : hidden = hidden' := by
    simpa using congrArg Prod.fst hTail
  have hCode : foldSquarefreeCode choices = foldSquarefreeCode choices' := by
    simpa using congrArg Prod.snd hTail
  have hChoices : choices = choices' := foldSquarefreeCode_injective hCode
  subst hBase
  subst hHidden
  subst hChoices
  rfl

/-- The squarefree externalization restricted to its image. -/
noncomputable def foldPsiToRange (m : ℕ) : FoldOmega m → Set.range (foldPsi m) :=
  fun ω => ⟨foldPsi m ω, ⟨ω, rfl⟩⟩

theorem foldPsiToRange_bijective (m : ℕ) : Function.Bijective (foldPsiToRange m) := by
  constructor
  · intro ω ω' h
    apply foldPsi_injective m
    simpa [foldPsiToRange] using congrArg Subtype.val h
  · intro y
    rcases y with ⟨val, ⟨ω, hω⟩⟩
    subst val
    exact ⟨ω, rfl⟩

/-- Paper-facing package: the prime-register object remains initial, squarefree externalization is
injective, and restricting to the image gives an explicit bijection.
    thm:group-jg-fold-squarefree-externalization -/
theorem paper_group_jg_fold_squarefree_externalization :
    (∀ E : GShiftEncoder, PrimeRegisterInitialFor E) ∧
    (∀ m : ℕ, Function.Injective (foldPsi m)) ∧
    (∀ m : ℕ, Function.Bijective (foldPsiToRange m)) := by
  exact ⟨paper_group_jg_prime_register_initial_object, foldPsi_injective, foldPsiToRange_bijective⟩

end Omega.GroupUnification
