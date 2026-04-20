import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.POM

open Matrix

/-- Positive rational points used for the ping-pong action. -/
abbrev PosRat := {x : ℚ // 0 < x}

/-- Basepoint `1 ∈ (0, ∞)`. -/
def posOne : PosRat := ⟨1, by positivity⟩

/-- The interval anchor attached to the `i`th generator. -/
def primeDetBase {k : ℕ} (i : Fin k) : ℕ :=
  2 * i.1 + 2

/-- The `i`th encoding matrix. -/
def primeDetGenMatrix {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k) :
    Matrix (Fin 2) (Fin 2) ℕ :=
  !![primeDetBase i * N + p i, primeDetBase i; N, 1]

/-- The matrix encoding of a word. -/
def primeDetWordMatrix {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (w : List (Fin k)) :
    Matrix (Fin 2) (Fin 2) ℕ :=
  (w.map (primeDetGenMatrix N p)).prod

/-- The fractional-linear action of the `i`th generator. -/
def primeDetGenActionVal {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k) (t : ℚ) : ℚ :=
  (((primeDetBase i * N + p i : ℚ) * t + primeDetBase i) / ((N : ℚ) * t + 1))

/-- The `i`th generator preserves `(0, ∞)`. -/
def primeDetGenAction {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k) (x : PosRat) : PosRat := by
  refine ⟨primeDetGenActionVal N p i x.1, ?_⟩
  unfold primeDetGenActionVal primeDetBase
  have hx : 0 < x.1 := x.2
  have hden : 0 < (N : ℚ) * x.1 + 1 := by positivity
  positivity

/-- The ping-pong action of a word on `(0, ∞)`. -/
def primeDetWordAction {k : ℕ} (N : ℕ) (p : Fin k → ℕ) :
    List (Fin k) → PosRat → PosRat
  | [] => id
  | i :: w => primeDetGenAction N p i ∘ primeDetWordAction N p w

/-- Evaluate a matrix on a positive rational point. -/
def primeDetMatrixEval (A : Matrix (Fin 2) (Fin 2) ℕ) (x : PosRat) : ℚ :=
  (((A 0 0 : ℚ) * x.1 + A 0 1) / ((A 1 0 : ℚ) * x.1 + A 1 1))

lemma primeDetWordMatrix_bottom_right_pos {k : ℕ} (N : ℕ) (p : Fin k → ℕ)
    (w : List (Fin k)) : 0 < primeDetWordMatrix N p w 1 1 := by
  induction w with
  | nil =>
      simp [primeDetWordMatrix]
  | cons i w ih =>
      have hnonneg : 0 ≤ N * primeDetWordMatrix N p w 0 1 := Nat.zero_le _
      have hpos : 0 < primeDetWordMatrix N p w 1 1 := ih
      simpa [primeDetWordMatrix, primeDetGenMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
        (show 0 < N * primeDetWordMatrix N p w 0 1 + primeDetWordMatrix N p w 1 1 by omega)

lemma primeDetWordMatrix_den_pos {k : ℕ} (N : ℕ) (p : Fin k → ℕ)
    (w : List (Fin k)) (x : PosRat) :
    0 < (primeDetWordMatrix N p w 1 0 : ℚ) * x.1 + primeDetWordMatrix N p w 1 1 := by
  have hEntry : 0 ≤ (primeDetWordMatrix N p w 1 0 : ℚ) := by
    exact_mod_cast (Nat.zero_le (primeDetWordMatrix N p w 1 0))
  have hx : 0 ≤ x.1 := le_of_lt x.2
  have h1 : 0 ≤ (primeDetWordMatrix N p w 1 0 : ℚ) * x.1 := by
    exact mul_nonneg hEntry hx
  have h2 : 0 < (primeDetWordMatrix N p w 1 1 : ℚ) := by
    exact_mod_cast primeDetWordMatrix_bottom_right_pos N p w
  linarith

lemma primeDetGenAction_sub_base {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k) (x : PosRat) :
    primeDetGenActionVal N p i x.1 - primeDetBase i =
      ((p i : ℚ) * x.1) / ((N : ℚ) * x.1 + 1) := by
  have hden : ((N : ℚ) * x.1 + 1) ≠ 0 := by
    have hden' : 0 < (N : ℚ) * x.1 + 1 := by
      have hNx : 0 ≤ (N : ℚ) * x.1 := by
        exact mul_nonneg (by exact_mod_cast (Nat.zero_le N)) (le_of_lt x.2)
      linarith
    exact hden'.ne'
  unfold primeDetGenActionVal primeDetBase
  field_simp [hden]
  ring

lemma primeDetGenAction_floor {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k)
    (_hN : 1 ≤ N) (hprime : Nat.Prime (p i)) (hbound : p i < N) (x : PosRat) :
    Int.floor ((primeDetGenAction N p i x).1) = primeDetBase i := by
  change Int.floor (primeDetGenActionVal N p i x.1) = primeDetBase i
  have hsub := primeDetGenAction_sub_base N p i x
  have hp : (0 : ℚ) < p i := by exact_mod_cast hprime.pos
  have hden : 0 < (N : ℚ) * x.1 + 1 := by
    have hNx : 0 ≤ (N : ℚ) * x.1 := by
      exact mul_nonneg (by exact_mod_cast (Nat.zero_le N)) (le_of_lt x.2)
    linarith
  have hbase_lt : (primeDetBase i : ℚ) < primeDetGenActionVal N p i x.1 := by
    have hfrac : 0 < ((p i : ℚ) * x.1) / ((N : ℚ) * x.1 + 1) := by
      apply div_pos
      exact mul_pos hp x.2
      exact hden
    linarith
  have hupper : primeDetGenActionVal N p i x.1 < primeDetBase i + 1 := by
    have hpN : (p i : ℚ) < N := by exact_mod_cast hbound
    have hlt : ((p i : ℚ) * x.1) < (N : ℚ) * x.1 + 1 := by
      nlinarith [x.2, hpN]
    have hfrac_lt : ((p i : ℚ) * x.1) / ((N : ℚ) * x.1 + 1) < 1 := by
      exact (div_lt_one hden).2 hlt
    linarith [hsub]
  exact Int.floor_eq_iff.mpr ⟨le_of_lt hbase_lt, by simpa using hupper⟩

lemma primeDetGenAction_injective {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k)
    (hprime : Nat.Prime (p i)) :
    Function.Injective (primeDetGenAction N p i) := by
  intro x y hxy
  apply Subtype.ext
  have hval : ((primeDetGenAction N p i x).1 : ℚ) = (primeDetGenAction N p i y).1 := by
    exact congrArg Subtype.val hxy
  have hxden : ((N : ℚ) * x.1 + 1) ≠ 0 := by
    have : 0 < (N : ℚ) * x.1 + 1 := by
      have hNx : 0 ≤ (N : ℚ) * x.1 := by
        exact mul_nonneg (by exact_mod_cast (Nat.zero_le N)) (le_of_lt x.2)
      linarith
    exact this.ne'
  have hyden : ((N : ℚ) * y.1 + 1) ≠ 0 := by
    have : 0 < (N : ℚ) * y.1 + 1 := by
      have hNy : 0 ≤ (N : ℚ) * y.1 := by
        exact mul_nonneg (by exact_mod_cast (Nat.zero_le N)) (le_of_lt y.2)
      linarith
    exact this.ne'
  have hp : (0 : ℚ) < p i := by exact_mod_cast hprime.pos
  change primeDetGenActionVal N p i x.1 = primeDetGenActionVal N p i y.1 at hval
  unfold primeDetGenActionVal primeDetBase at hval
  field_simp [hxden, hyden] at hval
  nlinarith

lemma primeDetHeadFloor {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k) (w : List (Fin k))
    (hN : 1 ≤ N) (hprime : ∀ j, Nat.Prime (p j)) (hbound : ∀ j, p j < N) :
    Int.floor ((primeDetWordAction N p (i :: w) posOne).1) = primeDetBase i := by
  simpa [primeDetWordAction] using
    primeDetGenAction_floor N p i hN (hprime i) (hbound i) (primeDetWordAction N p w posOne)

lemma primeDetWordAction_injective {k : ℕ} (N : ℕ) (p : Fin k → ℕ)
    (hN : 1 ≤ N) (hprime : ∀ i, Nat.Prime (p i)) (hbound : ∀ i, p i < N) :
    Function.Injective (primeDetWordAction N p) := by
  intro u
  induction u with
  | nil =>
      intro v hv
      cases v with
      | nil => rfl
      | cons j v =>
          have hval : ((primeDetWordAction N p (j :: v) posOne).1 : ℚ) = 1 := by
            exact congrArg Subtype.val (congrFun hv posOne).symm
          have hfloor := primeDetHeadFloor N p j v hN hprime hbound
          rw [hval] at hfloor
          norm_num at hfloor
          have hbasej : primeDetBase j = 1 := by exact_mod_cast hfloor.symm
          dsimp [primeDetBase] at hbasej
          omega
  | cons i u ihu =>
      intro v hv
      cases v with
      | nil =>
          have hval : ((primeDetWordAction N p (i :: u) posOne).1 : ℚ) = 1 := by
            exact congrArg Subtype.val (congrFun hv posOne)
          have hfloor := primeDetHeadFloor N p i u hN hprime hbound
          rw [hval] at hfloor
          norm_num at hfloor
          have hbasei : primeDetBase i = 1 := by exact_mod_cast hfloor.symm
          dsimp [primeDetBase] at hbasei
          omega
      | cons j v =>
          have hi := primeDetHeadFloor N p i u hN hprime hbound
          have hj := primeDetHeadFloor N p j v hN hprime hbound
          have hval : ((primeDetWordAction N p (i :: u) posOne).1 : ℚ) =
              (primeDetWordAction N p (j :: v) posOne).1 := by
            exact congrArg Subtype.val (congrFun hv posOne)
          rw [hval] at hi
          have hijBase : primeDetBase i = primeDetBase j := by
            exact_mod_cast hi.symm.trans hj
          have hijNat : i.1 = j.1 := by
            dsimp [primeDetBase] at hijBase
            omega
          have hij : i = j := Fin.ext hijNat
          subst hij
          have htail : primeDetWordAction N p u = primeDetWordAction N p v := by
            funext x
            apply primeDetGenAction_injective N p i (hprime i)
            exact congrFun hv x
          exact congrArg (List.cons i) (ihu htail)

lemma primeDetMatrixEval_gen_mul {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (i : Fin k)
    (B : Matrix (Fin 2) (Fin 2) ℕ) (x : PosRat)
    (hden : ((B 1 0 : ℚ) * x.1 + B 1 1) ≠ 0)
    (hpos : 0 < primeDetMatrixEval B x) :
    primeDetMatrixEval (primeDetGenMatrix N p i * B) x =
      primeDetGenActionVal N p i (primeDetMatrixEval B x) := by
  have houter : ((N : ℚ) * primeDetMatrixEval B x + 1) ≠ 0 := by
    have : 0 < (N : ℚ) * primeDetMatrixEval B x + 1 := by
      have hNx : 0 ≤ (N : ℚ) * primeDetMatrixEval B x := by
        exact mul_nonneg (by exact_mod_cast (Nat.zero_le N)) (le_of_lt hpos)
      linarith
    exact this.ne'
  unfold primeDetMatrixEval primeDetGenMatrix primeDetGenActionVal primeDetBase
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp [hden, houter]
  ring

lemma primeDetMatrixEval_word {k : ℕ} (N : ℕ) (p : Fin k → ℕ) (w : List (Fin k))
    (x : PosRat) :
    primeDetMatrixEval (primeDetWordMatrix N p w) x = (primeDetWordAction N p w x).1 := by
  induction w with
  | nil =>
      simp [primeDetWordMatrix, primeDetWordAction, primeDetMatrixEval]
  | cons i w ih =>
      have hden : ((primeDetWordMatrix N p w 1 0 : ℚ) * x.1 + primeDetWordMatrix N p w 1 1) ≠ 0 :=
        (primeDetWordMatrix_den_pos N p w x).ne'
      have hpos : 0 < primeDetMatrixEval (primeDetWordMatrix N p w) x := by
        rw [ih]
        exact (primeDetWordAction N p w x).2
      calc
        primeDetMatrixEval (primeDetWordMatrix N p (i :: w)) x
            = primeDetGenActionVal N p i (primeDetMatrixEval (primeDetWordMatrix N p w) x) := by
                simpa [primeDetWordMatrix] using
                  primeDetMatrixEval_gen_mul N p i (primeDetWordMatrix N p w) x hden hpos
        _ = primeDetGenActionVal N p i ((primeDetWordAction N p w x).1) := by rw [ih]
        _ = (primeDetWordAction N p (i :: w) x).1 := rfl

/-- Explicit `2 × 2` generators with prime determinants give a free word encoding:
each generator has the prescribed determinant, and the induced word matrix map is injective.
    prop:pom-prime-determinant-2x2-free-encoding -/
theorem paper_pom_prime_determinant_2x2_free_encoding
    {k N : ℕ} (p : Fin k → ℕ) (hprime : ∀ i, Nat.Prime (p i)) (hN : 1 ≤ N)
    (hbound : ∀ i, p i < N) :
    (∀ i, ((primeDetGenMatrix N p i).map Int.ofNatHom).det = p i) ∧
      Function.Injective (primeDetWordMatrix N p) := by
  refine ⟨?_, ?_⟩
  · intro i
    unfold primeDetGenMatrix primeDetBase
    simp [Matrix.det_fin_two]
  · intro u v h
    apply primeDetWordAction_injective N p hN hprime hbound
    funext x
    apply Subtype.ext
    simpa [primeDetMatrixEval_word] using congrArg (fun A => primeDetMatrixEval A x) h

end Omega.POM
