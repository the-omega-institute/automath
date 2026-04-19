import Mathlib.Tactic

namespace Omega.POM

/-- Concrete package for the extended primitive generators: zero, successor, pairing, and the
division-section output, together with the two observable projections. -/
structure ExtendedPrimitiveData where
  zeroGen : Nat
  succGen : Nat → Nat
  pairGen : Nat → Nat → Nat × Nat
  divSectionGen : Nat → Nat → Nat × Nat
  outLeft : Nat × Nat → Nat
  outRight : Nat × Nat → Nat
  hzero : zeroGen = 0
  hsucc : succGen = Nat.succ
  hpair : pairGen = Prod.mk
  hdivSection : divSectionGen = fun a b => (a / b, a % b)
  houtLeft : outLeft = Prod.fst
  houtRight : outRight = Prod.snd

namespace ExtendedPrimitiveData

def addState (D : ExtendedPrimitiveData) (a : Nat) : Nat → Nat × Nat
  | 0 => D.pairGen a D.zeroGen
  | n + 1 =>
      let st := addState D a n
      D.pairGen (D.succGen (D.outLeft st)) (D.outRight st)

def addOp (D : ExtendedPrimitiveData) (a b : Nat) : Nat :=
  D.outLeft (D.addState a b)

def mulState (D : ExtendedPrimitiveData) (b : Nat) : Nat → Nat × Nat
  | 0 => D.pairGen D.zeroGen b
  | n + 1 =>
      let st := mulState D b n
      D.pairGen (D.addOp (D.outLeft st) (D.outRight st)) (D.outRight st)

def mulOp (D : ExtendedPrimitiveData) (a b : Nat) : Nat :=
  D.outLeft (D.mulState b a)

def divPair (D : ExtendedPrimitiveData) (a b : Nat) : Nat × Nat :=
  D.divSectionGen a b

def quoOp (D : ExtendedPrimitiveData) (a b : Nat) : Nat :=
  D.outLeft (D.divPair a b)

def remOp (D : ExtendedPrimitiveData) (a b : Nat) : Nat :=
  D.outRight (D.divPair a b)

def processLayer (D : ExtendedPrimitiveData) (a b : Nat) : Nat × Nat :=
  D.pairGen (D.addOp a b) (D.quoOp a (b + 1))

def addGenerated (D : ExtendedPrimitiveData) : Prop :=
  ∀ a b, D.addOp a b = a + b

def mulGenerated (D : ExtendedPrimitiveData) : Prop :=
  ∀ a b, D.mulOp a b = a * b

def divGenerated (D : ExtendedPrimitiveData) : Prop :=
  ∀ a b, D.divPair a b = (a / b, a % b)

def quoGenerated (D : ExtendedPrimitiveData) : Prop :=
  ∀ a b, D.quoOp a b = a / b

def remGenerated (D : ExtendedPrimitiveData) : Prop :=
  ∀ a b, D.remOp a b = a % b

def processLayerNormalForm (D : ExtendedPrimitiveData) : Prop :=
  ∀ a b,
    D.pairGen (D.outLeft (D.processLayer a b)) (D.outRight (D.processLayer a b)) =
      D.processLayer a b

@[simp] lemma outLeft_pair (D : ExtendedPrimitiveData) (x y : Nat) :
    D.outLeft (D.pairGen x y) = x := by
  rw [D.houtLeft, D.hpair]

@[simp] lemma outRight_pair (D : ExtendedPrimitiveData) (x y : Nat) :
    D.outRight (D.pairGen x y) = y := by
  rw [D.houtRight, D.hpair]

lemma addState_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.addState a b = (a + b, 0) := by
  induction b with
  | zero =>
      simp [addState, D.hpair, D.hzero]
  | succ b ih =>
      simp [addState, ih, D.hpair, D.hsucc, D.houtLeft, D.houtRight, Nat.add_assoc]

lemma addOp_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.addOp a b = a + b := by
  simp [addOp, D.addState_eq, D.houtLeft]

lemma mulState_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.mulState b a = (a * b, b) := by
  induction a with
  | zero =>
      simp [mulState, D.hpair, D.hzero]
  | succ a ih =>
      simp [mulState, ih, D.addOp_eq, D.hpair, D.houtLeft, D.houtRight, Nat.succ_mul,
        Nat.add_comm]

lemma mulOp_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.mulOp a b = a * b := by
  simp [mulOp, D.mulState_eq, D.houtLeft]

lemma divPair_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.divPair a b = (a / b, a % b) := by
  simp [divPair, D.hdivSection]

lemma quoOp_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.quoOp a b = a / b := by
  simp [quoOp, D.divPair_eq, D.houtLeft]

lemma remOp_eq (D : ExtendedPrimitiveData) (a b : Nat) : D.remOp a b = a % b := by
  simp [remOp, D.divPair_eq, D.houtRight]

lemma processLayerNormalForm_proof (D : ExtendedPrimitiveData) (a b : Nat) :
    D.pairGen (D.outLeft (D.processLayer a b)) (D.outRight (D.processLayer a b)) =
      D.processLayer a b := by
  simp [processLayer, D.hpair, D.houtLeft, D.houtRight]

end ExtendedPrimitiveData

/-- Paper wrapper for the extended primitive package: the four primitive generators together with
the two projections generate addition, multiplication, division, quotient, remainder, and the
process-layer normal form. `thm:pom-extended-primitives` -/
theorem paper_pom_extended_primitives (D : ExtendedPrimitiveData) :
    D.addGenerated ∧ D.mulGenerated ∧ D.divGenerated ∧ D.quoGenerated ∧ D.remGenerated ∧
      D.processLayerNormalForm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact D.addOp_eq a b
  · intro a b
    exact D.mulOp_eq a b
  · intro a b
    exact D.divPair_eq a b
  · intro a b
    exact D.quoOp_eq a b
  · intro a b
    exact D.remOp_eq a b
  · intro a b
    exact D.processLayerNormalForm_proof a b

end Omega.POM
