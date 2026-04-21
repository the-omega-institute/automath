import Mathlib.Data.Fintype.Card
import Omega.Core.Fib
import Omega.POM.KLDefectIdentity
import Omega.POM.MaxentLift
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

/-- Any external ledger alphabet that is injective on the explicit fixed target fiber must have at
least `2^n` symbols, because that fiber already contains `2^n` words. -/
theorem paper_fold_fixed_fiber_external_ledger_linear (n : ℕ) {R : Type} [Fintype R]
    (r : FoldFibreStarWord n -> R)
    (hinj : Function.Injective fun x : {x // x ∈ foldFibreStarFiber n} => r x.1) :
    2 ^ n <= Fintype.card R := by
  classical
  have hcard : Fintype.card ↥(foldFibreStarFiber n) ≤ Fintype.card R :=
    Fintype.card_le_of_injective _ hinj
  have hmult_card : Fintype.card ↥(foldFibreStarFiber n) = foldFibreStarMultiplicity n := by
    simpa [foldFibreStarMultiplicity] using (Fintype.card_coe (foldFibreStarFiber n))
  have hmult : foldFibreStarMultiplicity n ≤ Fintype.card R := by
    rw [← hmult_card]
    exact hcard
  exact (paper_fold_fibre_star_exp_lb n).trans hmult

/-- The one-point macrostate used to package the ledger identity for the fixed target fiber. -/
abbrev FoldFibreStarLedgerMacrostate := PUnit

/-- Fiber degree of the ledger model: the single macrostate has `2^n` microstates. -/
def foldFibreStarLedgerDegree (n : ℕ) : FoldFibreStarLedgerMacrostate → ℕ :=
  fun _ => 2 ^ n

/-- Dirac macro-distribution at the unique target macrostate. -/
def foldFibreStarLedgerMacroDist (n : ℕ) : FoldFibreStarLedgerMacrostate → ℝ :=
  fun _ => 1

/-- The uniform lift over the one-point macrostate with `2^n` microstates. -/
noncomputable def foldFibreStarLedgerMicroDist (n : ℕ) :
    Omega.POM.FiberMicrostate (foldFibreStarLedgerDegree n) → ℝ :=
  Omega.POM.fiberUniformLift (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMacroDist n)

lemma foldFibreStarImage_card (n : ℕ) :
    (Finset.univ.image (foldFibreStarEncode (n := n))).card = 2 ^ n := by
  classical
  rw [Finset.card_image_of_injective]
  · simp [FoldFibreStarBitstring, Fintype.card_bool, Fintype.card_fin]
  · exact foldFibreStarEncode_injective n

lemma foldFibreStar_log_two_pow (n : ℕ) :
    Real.log ((2 ^ n : ℕ) : ℝ) = n * Real.log 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hx : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
      have hy : (2 : ℝ) ≠ 0 := by norm_num
      rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul hx hy]
      rw [ih]
      calc
        (n : ℝ) * Real.log 2 + Real.log 2 = (((n : ℝ) + 1) * Real.log 2) := by ring
        _ = Real.log 2 * (((n : ℝ) + 1)) := by ring
        _ = Real.log 2 * (↑(n + 1)) := by norm_num
        _ = ↑(n + 1) * Real.log 2 := by ring

private lemma foldFibreStarLedgerDegree_pos (n : ℕ) (x : FoldFibreStarLedgerMacrostate) :
    0 < foldFibreStarLedgerDegree n x := by
  simp [foldFibreStarLedgerDegree]

private lemma foldFibreStarLedgerMarginal (n : ℕ) (x : FoldFibreStarLedgerMacrostate) :
    Omega.POM.fiberMarginal (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMicroDist n) x =
      foldFibreStarLedgerMacroDist n x := by
  have hd : 0 < foldFibreStarLedgerDegree n x := foldFibreStarLedgerDegree_pos n x
  have hd0 : ((foldFibreStarLedgerDegree n x : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  calc
    Omega.POM.fiberMarginal (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMicroDist n) x
        = ∑ _i : Fin (foldFibreStarLedgerDegree n x),
            (foldFibreStarLedgerMacroDist n x : ℝ) / foldFibreStarLedgerDegree n x := by
              simp [Omega.POM.fiberMarginal, foldFibreStarLedgerMicroDist, Omega.POM.fiberUniformLift]
    _ = ((foldFibreStarLedgerDegree n x : ℕ) : ℝ) *
          ((foldFibreStarLedgerMacroDist n x : ℝ) / foldFibreStarLedgerDegree n x) := by
            simp
    _ = foldFibreStarLedgerMacroDist n x := by
          field_simp [hd0]

private lemma foldFibreStarLedgerMicroNonneg (n : ℕ) :
    ∀ a, 0 ≤ foldFibreStarLedgerMicroDist n a := by
  intro a
  simp [foldFibreStarLedgerMicroDist, foldFibreStarLedgerMacroDist, Omega.POM.fiberUniformLift]

private lemma foldFibreStarLedgerMacroNonneg (n : ℕ) :
    ∀ x, 0 ≤ foldFibreStarLedgerMacroDist n x := by
  intro x
  simp [foldFibreStarLedgerMacroDist]

private lemma foldFibreStarLedgerMicroSum (n : ℕ) :
    Finset.univ.sum (foldFibreStarLedgerMicroDist n) = 1 := by
  rw [Fintype.sum_sigma]
  simpa [Omega.POM.fiberMarginal] using foldFibreStarLedgerMarginal n PUnit.unit

private lemma foldFibreStarLedgerEntropy (n : ℕ) :
    Omega.POM.liftEntropy (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMicroDist n) =
      Real.log ((2 ^ n : ℕ) : ℝ) := by
  have hmaxent :=
    Omega.POM.paper_pom_maxent_lift
      (foldFibreStarLedgerDegree n) (foldFibreStarLedgerDegree_pos n) (foldFibreStarLedgerMacroDist n)
      (foldFibreStarLedgerMicroDist n) (by intro x i j; rfl) (foldFibreStarLedgerMarginal n)
  rcases hmaxent with ⟨_, hEntropy⟩
  simpa [foldFibreStarLedgerMacroDist, foldFibreStarLedgerDegree] using hEntropy

private lemma foldFibreStarLedgerKlZero (n : ℕ) :
    Omega.POM.klDiv (foldFibreStarLedgerMicroDist n)
      (Omega.POM.fiberUniformLift (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMacroDist n)) = 0 := by
  have hkl :=
    Omega.POM.paper_pom_kl_defect_identity
      (foldFibreStarLedgerDegree n) (foldFibreStarLedgerDegree_pos n) (foldFibreStarLedgerMacroDist n)
      (foldFibreStarLedgerMicroDist n) (foldFibreStarLedgerMarginal n) (foldFibreStarLedgerMicroNonneg n)
      (foldFibreStarLedgerMacroNonneg n) (foldFibreStarLedgerMicroSum n)
  simpa [foldFibreStarLedgerMicroDist] using hkl

/-- The explicit `100/011` encoder has zero macro entropy at the common target macrostate, linear
source entropy `n log 2`, and the corresponding finite-fiber ledger identity closes with zero KL
defect on the uniform lift.
    prop:fold-fiber-ledger-zero-macro-linear-micro -/
theorem paper_fold_fiber_ledger_zero_macro_linear_micro (n : ℕ) :
    (∀ w : FoldFibreStarBitstring n,
      foldFibreStarWeight (foldFibreStarEncode w) = foldFibreStarTargetWeight n) ∧
    Real.negMulLog (foldFibreStarLedgerMacroDist n PUnit.unit) = 0 ∧
    Real.log (((Finset.univ.image (foldFibreStarEncode (n := n))).card : ℝ)) = n * Real.log 2 ∧
    Omega.POM.liftEntropy (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMicroDist n) =
      n * Real.log 2 ∧
    Omega.POM.liftEntropy (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMicroDist n) =
      Real.log ((foldFibreStarLedgerDegree n PUnit.unit : ℕ) : ℝ) -
        Omega.POM.klDiv (foldFibreStarLedgerMicroDist n)
          (Omega.POM.fiberUniformLift (foldFibreStarLedgerDegree n) (foldFibreStarLedgerMacroDist n)) ∧
    2 ^ n ≤ foldFibreStarMultiplicity n := by
  refine ⟨foldFibreStarEncode_weight, ?_, ?_, ?_, ?_, paper_fold_fibre_star_exp_lb n⟩
  · simp [foldFibreStarLedgerMacroDist]
  · rw [foldFibreStarImage_card, foldFibreStar_log_two_pow]
  · rw [foldFibreStarLedgerEntropy, foldFibreStar_log_two_pow]
  · rw [foldFibreStarLedgerEntropy, foldFibreStarLedgerKlZero]
    simp [foldFibreStarLedgerDegree]

end

end Omega
