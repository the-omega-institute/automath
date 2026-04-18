import Mathlib.Data.Fintype.Card
import Omega.Core.Fib
import Mathlib.Tactic

namespace Omega

noncomputable section

open scoped BigOperators

/-- Length-`n` input bitstrings for the explicit three-block encoder. -/
abbrev FoldFibreStarBitstring (n : ℕ) := Fin n → Bool

/-- Words of length `3n`, organized as `n` consecutive blocks of length `3`. -/
abbrev FoldFibreStarWord (n : ℕ) := Fin n → Fin 3 → Bool

/-- The two allowed triples: `100` for `false` and `011` for `true`. -/
def foldFibreStarEncodeBlock (b : Bool) : Fin 3 → Bool
  | 0 => !b
  | 1 => b
  | _ => b

/-- The blockwise encoder from `n` bits to `3n` bits. -/
def foldFibreStarEncode (w : FoldFibreStarBitstring n) : FoldFibreStarWord n :=
  fun i j => foldFibreStarEncodeBlock (w i) j

/-- The target stable block `100`. -/
def foldFibreStarTargetBlock : Fin 3 → Bool
  | 0 => true
  | _ => false

/-- The per-position Fibonacci weight inside the `i`-th block. -/
def foldFibreStarPositionWeight (i : Fin n) : Fin 3 → ℕ
  | 0 => Nat.fib (3 * i.1 + 3)
  | 1 => Nat.fib (3 * i.1 + 2)
  | _ => Nat.fib (3 * i.1 + 1)

/-- The Fibonacci weight carried by a single block. -/
def foldFibreStarBlockWeight (i : Fin n) (block : Fin 3 → Bool) : ℕ :=
  ∑ j : Fin 3, if block j then foldFibreStarPositionWeight i j else 0

/-- The total Fibonacci weight of a `3n`-word. -/
def foldFibreStarWeight (word : FoldFibreStarWord n) : ℕ :=
  ∑ i : Fin n, foldFibreStarBlockWeight i (word i)

/-- The target weight contributed by the stable block `100` in each fiber. -/
def foldFibreStarTargetWeight (n : ℕ) : ℕ :=
  ∑ i : Fin n, Nat.fib (3 * i.1 + 3)

/-- The concrete fiber over the common target Fibonacci weight. -/
def foldFibreStarFiber (n : ℕ) : Finset (FoldFibreStarWord n) := by
  classical
  exact Finset.univ.filter fun word => foldFibreStarWeight word = foldFibreStarTargetWeight n

@[simp] lemma mem_foldFibreStarFiber {n : ℕ} {word : FoldFibreStarWord n} :
    word ∈ foldFibreStarFiber n ↔ foldFibreStarWeight word = foldFibreStarTargetWeight n := by
  classical
  simp [foldFibreStarFiber]

/-- The associated multiplicity. -/
def foldFibreStarMultiplicity (n : ℕ) : ℕ :=
  (foldFibreStarFiber n).card

lemma foldFibreStarEncodeBlockWeight (i : Fin n) (b : Bool) :
    foldFibreStarBlockWeight i (foldFibreStarEncodeBlock b) = Nat.fib (3 * i.1 + 3) := by
  cases b
  · simp [foldFibreStarBlockWeight, foldFibreStarEncodeBlock, foldFibreStarPositionWeight,
      Fin.sum_univ_three]
  · simp [foldFibreStarBlockWeight, foldFibreStarEncodeBlock, foldFibreStarPositionWeight,
      Fin.sum_univ_three]
    have hf : Nat.fib (3 + 3 * i.1) = Nat.fib (1 + 3 * i.1) + Nat.fib (2 + 3 * i.1) := by
      rw [show 3 + 3 * i.1 = (1 + 3 * i.1) + 2 by omega, Nat.fib_add_two]
      congr 2 <;> omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hf.symm

lemma foldFibreStarEncode_weight (w : FoldFibreStarBitstring n) :
    foldFibreStarWeight (foldFibreStarEncode w) = foldFibreStarTargetWeight n := by
  unfold foldFibreStarWeight foldFibreStarTargetWeight foldFibreStarEncode
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa using foldFibreStarEncodeBlockWeight i (w i)

lemma foldFibreStarEncode_injective (n : ℕ) :
    Function.Injective (foldFibreStarEncode (n := n)) := by
  intro w₁ w₂ h
  funext i
  have hmid := congrArg (fun word => word i 1) h
  simpa [foldFibreStarEncode, foldFibreStarEncodeBlock] using hmid

/-- The encoder lands in the single target-weight fiber. -/
def foldFibreStarLift (n : ℕ) : FoldFibreStarBitstring n → ↥(foldFibreStarFiber n) :=
  fun w => ⟨foldFibreStarEncode w, by simpa using foldFibreStarEncode_weight w⟩

lemma foldFibreStarLift_injective (n : ℕ) :
    Function.Injective (foldFibreStarLift n) := by
  intro w₁ w₂ h
  apply foldFibreStarEncode_injective n
  exact congrArg Subtype.val h

/-- The explicit `100/011` block encoder injects `2^n` bitstrings into a single fixed fiber, giving
an exponential lower bound on that fiber cardinality.
    cor:fold-fibre-star-exp-lb -/
theorem paper_fold_fibre_star_exp_lb :
    ∀ n : ℕ, 2 ^ n ≤ foldFibreStarMultiplicity n := by
  intro n
  classical
  calc
    2 ^ n = Fintype.card (FoldFibreStarBitstring n) := by
      simp [FoldFibreStarBitstring, Fintype.card_bool, Fintype.card_fin]
    _ ≤ Fintype.card ↥(foldFibreStarFiber n) :=
      Fintype.card_le_of_injective (foldFibreStarLift n) (foldFibreStarLift_injective n)
    _ = foldFibreStarMultiplicity n := by
      simpa [foldFibreStarMultiplicity] using (Fintype.card_coe (foldFibreStarFiber n))

end

end Omega
