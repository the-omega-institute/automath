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

/-- Signed literals for a concrete three-CNF syntax. -/
inductive FoldFibreLiteral (α : Type*)
  | pos : α → FoldFibreLiteral α
  | neg : α → FoldFibreLiteral α

/-- A three-literal clause. -/
abbrev FoldFibreClause (α : Type*) := Fin 3 → FoldFibreLiteral α

/-- A three-CNF formula is a list of three-literal clauses. -/
abbrev FoldFibreThreeCNF (α : Type*) := List (FoldFibreClause α)

/-- Satisfaction of a single signed literal. -/
def foldFibreLiteralSatisfied {α : Type*} (assignment : α → Bool) :
    FoldFibreLiteral α → Prop
  | .pos v => assignment v = true
  | .neg v => assignment v = false

/-- Satisfaction of a single three-literal clause. -/
def foldFibreClauseSatisfied {α : Type*} (assignment : α → Bool) (clause : FoldFibreClause α) :
    Prop :=
  ∃ j : Fin 3, foldFibreLiteralSatisfied assignment (clause j)

/-- Recursive satisfaction for a concrete three-CNF formula. -/
def foldFibreFormulaSatisfied {α : Type*} (assignment : α → Bool) :
    FoldFibreThreeCNF α → Prop
  | [] => True
  | clause :: formula =>
      foldFibreClauseSatisfied assignment clause ∧ foldFibreFormulaSatisfied assignment formula

/-- Witness-based satisfiability for the concrete three-CNF syntax. -/
def foldFibreFormulaSatisfiable {α : Type*} (formula : FoldFibreThreeCNF α) : Prop :=
  ∃ assignment : α → Bool, foldFibreFormulaSatisfied assignment formula

/-- The `3n` variables of the fixed-fiber language, arranged blockwise. -/
abbrev FoldFibre3SATVar (n : ℕ) := Fin n × Fin 3

/-- Three-CNF formulas over the blockwise `3n` variables. -/
abbrev FoldFibre3SATFormula (n : ℕ) := FoldFibreThreeCNF (FoldFibre3SATVar n)

/-- Read a blockwise word as a Boolean assignment on the `3n` variables. -/
def foldFibreWordAssignment (word : FoldFibreStarWord n) : FoldFibre3SATVar n → Bool
  | ⟨i, j⟩ => word i j

/-- Project a blockwise word to its middle coordinates. -/
def foldFibreMidAssignment (word : FoldFibreStarWord n) : Fin n → Bool :=
  fun i => word i 1

/-- Verifier for the fixed-fiber language: satisfy the formula and land in the common fixed fiber. -/
def foldFibre3SATVerifier (formula : FoldFibre3SATFormula n) (word : FoldFibreStarWord n) : Prop :=
  foldFibreFormulaSatisfied (foldFibreWordAssignment word) formula ∧ word ∈ foldFibreStarFiber n

/-- The fixed-fiber language: some witness in the common `100/011` fiber satisfies the formula. -/
def foldFibre3SATLanguage (formula : FoldFibre3SATFormula n) : Prop :=
  ∃ word : FoldFibreStarWord n, foldFibre3SATVerifier formula word

/-- Lift an `n`-variable literal to the middle coordinate of the corresponding block. -/
def foldFibreLiftLiteral : FoldFibreLiteral (Fin n) → FoldFibreLiteral (FoldFibre3SATVar n)
  | .pos i => .pos (i, 1)
  | .neg i => .neg (i, 1)

/-- Lift a clause by reading every variable through the block midpoint. -/
def foldFibreLiftClause (clause : FoldFibreClause (Fin n)) : FoldFibreClause (FoldFibre3SATVar n) :=
  fun j => foldFibreLiftLiteral (clause j)

/-- The blockwise SAT reduction: each original variable is read from the middle bit of its block. -/
def foldFibreLiftFormula : FoldFibreThreeCNF (Fin n) → FoldFibre3SATFormula n
  | [] => []
  | clause :: formula => foldFibreLiftClause clause :: foldFibreLiftFormula formula

lemma foldFibreLiteralSatisfied_lift_encode_iff (assignment : Fin n → Bool)
    (literal : FoldFibreLiteral (Fin n)) :
    foldFibreLiteralSatisfied (foldFibreWordAssignment (foldFibreStarEncode assignment))
        (foldFibreLiftLiteral literal) ↔
      foldFibreLiteralSatisfied assignment literal := by
  cases literal <;> simp [foldFibreLiteralSatisfied, foldFibreLiftLiteral, foldFibreWordAssignment,
    foldFibreStarEncode, foldFibreStarEncodeBlock]

lemma foldFibreLiteralSatisfied_lift_mid_iff (word : FoldFibreStarWord n)
    (literal : FoldFibreLiteral (Fin n)) :
    foldFibreLiteralSatisfied (foldFibreWordAssignment word) (foldFibreLiftLiteral literal) ↔
      foldFibreLiteralSatisfied (foldFibreMidAssignment word) literal := by
  cases literal <;> simp [foldFibreLiteralSatisfied, foldFibreLiftLiteral, foldFibreWordAssignment,
    foldFibreMidAssignment]

lemma foldFibreClauseSatisfied_lift_encode_iff (assignment : Fin n → Bool)
    (clause : FoldFibreClause (Fin n)) :
    foldFibreClauseSatisfied (foldFibreWordAssignment (foldFibreStarEncode assignment))
        (foldFibreLiftClause clause) ↔
      foldFibreClauseSatisfied assignment clause := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (foldFibreLiteralSatisfied_lift_encode_iff assignment (clause j)).1 hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (foldFibreLiteralSatisfied_lift_encode_iff assignment (clause j)).2 hj⟩

lemma foldFibreClauseSatisfied_lift_mid_iff (word : FoldFibreStarWord n)
    (clause : FoldFibreClause (Fin n)) :
    foldFibreClauseSatisfied (foldFibreWordAssignment word) (foldFibreLiftClause clause) ↔
      foldFibreClauseSatisfied (foldFibreMidAssignment word) clause := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (foldFibreLiteralSatisfied_lift_mid_iff word (clause j)).1 hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (foldFibreLiteralSatisfied_lift_mid_iff word (clause j)).2 hj⟩

lemma foldFibreFormulaSatisfied_lift_encode_iff (assignment : Fin n → Bool)
    (formula : FoldFibreThreeCNF (Fin n)) :
    foldFibreFormulaSatisfied (foldFibreWordAssignment (foldFibreStarEncode assignment))
        (foldFibreLiftFormula formula) ↔
      foldFibreFormulaSatisfied assignment formula := by
  induction formula with
  | nil =>
      simp [foldFibreLiftFormula, foldFibreFormulaSatisfied]
  | cons clause formula ih =>
      simp [foldFibreLiftFormula, foldFibreFormulaSatisfied,
        foldFibreClauseSatisfied_lift_encode_iff, ih]

lemma foldFibreFormulaSatisfied_lift_mid_iff (word : FoldFibreStarWord n)
    (formula : FoldFibreThreeCNF (Fin n)) :
    foldFibreFormulaSatisfied (foldFibreWordAssignment word) (foldFibreLiftFormula formula) ↔
      foldFibreFormulaSatisfied (foldFibreMidAssignment word) formula := by
  induction formula with
  | nil =>
      simp [foldFibreLiftFormula, foldFibreFormulaSatisfied]
  | cons clause formula ih =>
      simp [foldFibreLiftFormula, foldFibreFormulaSatisfied, foldFibreClauseSatisfied_lift_mid_iff,
        ih]

lemma foldFibre3SAT_reduction_spec (formula : FoldFibreThreeCNF (Fin n)) :
    foldFibreFormulaSatisfiable formula ↔ foldFibre3SATLanguage (foldFibreLiftFormula formula) := by
  constructor
  · rintro ⟨assignment, hassignment⟩
    refine ⟨foldFibreStarEncode assignment, ?_⟩
    refine ⟨(foldFibreFormulaSatisfied_lift_encode_iff assignment formula).2 hassignment, ?_⟩
    exact (mem_foldFibreStarFiber).2 (foldFibreStarEncode_weight assignment)
  · rintro ⟨word, hword⟩
    refine ⟨foldFibreMidAssignment word, ?_⟩
    exact (foldFibreFormulaSatisfied_lift_mid_iff word formula).1 hword.1

/-- Witness-based NP membership plus the blockwise reduction from 3SAT to the common fixed fiber.
    thm:fold-fibre-3sat-np-complete -/
def FoldFibre3SATNPComplete : Prop :=
  (∀ {n : ℕ} (formula : FoldFibre3SATFormula n), foldFibre3SATLanguage formula →
      ∃ word : FoldFibreStarWord n, foldFibre3SATVerifier formula word) ∧
    (∀ {n : ℕ} (formula : FoldFibreThreeCNF (Fin n)),
      foldFibreFormulaSatisfiable formula ↔ foldFibre3SATLanguage (foldFibreLiftFormula formula))

/-- Paper label: `thm:fold-fibre-3sat-np-complete`. The fixed target fiber already supports a
blockwise SAT reduction: the verifier checks a `3n`-variable three-CNF together with membership in
the common `100/011` fiber, and the middle coordinate of each block carries the original SAT
assignment. -/
theorem paper_fold_fibre_3sat_np_complete : FoldFibre3SATNPComplete := by
  refine ⟨?_, ?_⟩
  · intro n formula hformula
    exact hformula
  · intro n formula
    exact foldFibre3SAT_reduction_spec formula

/-- List-level version of the `100/011` encoder used to package many-one reductions on ordinary
bitstrings. -/
def fold_layerwise_degenerate_hardness_encode_list : List Bool → List Bool
  | [] => []
  | false :: tail => true :: false :: false :: fold_layerwise_degenerate_hardness_encode_list tail
  | true :: tail => false :: true :: true :: fold_layerwise_degenerate_hardness_encode_list tail

/-- Partial decoder for the list-level `100/011` code. -/
def fold_layerwise_degenerate_hardness_decode_list : List Bool → Option (List Bool)
  | [] => some []
  | true :: false :: false :: tail =>
      match fold_layerwise_degenerate_hardness_decode_list tail with
      | some word => some (false :: word)
      | none => none
  | false :: true :: true :: tail =>
      match fold_layerwise_degenerate_hardness_decode_list tail with
      | some word => some (true :: word)
      | none => none
  | _ => none

/-- Total decoder obtained by sending invalid words to a fixed rejecting string. -/
def fold_layerwise_degenerate_hardness_decode_or_reject (z0 : List Bool) (word : List Bool) :
    List Bool :=
  match fold_layerwise_degenerate_hardness_decode_list word with
  | some decoded => decoded
  | none => z0

/-- The layerwise-degenerate language consists of the encoded words whose decoder lands back in
the original language. -/
def fold_layerwise_degenerate_hardness_encoded_language (L : Set (List Bool)) (z0 : List Bool) :
    Set (List Bool) :=
  fun word => fold_layerwise_degenerate_hardness_decode_or_reject z0 word ∈ L

private lemma fold_layerwise_degenerate_hardness_decode_encode_list (word : List Bool) :
    fold_layerwise_degenerate_hardness_decode_list
        (fold_layerwise_degenerate_hardness_encode_list word) =
      some word := by
  induction word with
  | nil =>
      simp [fold_layerwise_degenerate_hardness_encode_list,
        fold_layerwise_degenerate_hardness_decode_list]
  | cons b tail ih =>
      cases b <;> simp [fold_layerwise_degenerate_hardness_encode_list,
        fold_layerwise_degenerate_hardness_decode_list, ih]

/-- Paper label: `prop:fold-layerwise-degenerate-hardness`. The explicit `100/011` encoding is a
many-one self-embedding of complexity into a single fixed fold fiber: encoding computes the
forward reduction, decoding with a fixed reject word computes the inverse reduction, invalid words
collapse to the designated reject string, and every encoded word lies in the common distinguished
fiber. -/
theorem paper_fold_layerwise_degenerate_hardness (L : Set (List Bool)) (z0 : List Bool)
    (hz0 : z0 ∉ L) :
    (∀ word,
      fold_layerwise_degenerate_hardness_encoded_language L z0
          (fold_layerwise_degenerate_hardness_encode_list word) ↔
        word ∈ L) ∧
      (∀ coded,
        fold_layerwise_degenerate_hardness_encoded_language L z0 coded ↔
          fold_layerwise_degenerate_hardness_decode_or_reject z0 coded ∈ L) ∧
      (∀ coded,
        fold_layerwise_degenerate_hardness_decode_list coded = none →
          ¬ fold_layerwise_degenerate_hardness_encoded_language L z0 coded) ∧
      (∀ n (word : FoldFibreStarBitstring n), foldFibreStarEncode word ∈ foldFibreStarFiber n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro word
    simp [fold_layerwise_degenerate_hardness_encoded_language,
      fold_layerwise_degenerate_hardness_decode_or_reject,
      fold_layerwise_degenerate_hardness_decode_encode_list]
  · intro coded
    rfl
  · intro coded hDecode hCoded
    have hz : z0 ∈ L := by
      simpa [fold_layerwise_degenerate_hardness_encoded_language,
        fold_layerwise_degenerate_hardness_decode_or_reject, hDecode] using hCoded
    exact hz0 hz
  · intro n word
    exact (mem_foldFibreStarFiber).2 (foldFibreStarEncode_weight word)

end

end Omega
