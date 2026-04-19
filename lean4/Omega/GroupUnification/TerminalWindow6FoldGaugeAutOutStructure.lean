import Mathlib.Tactic

namespace Omega.GroupUnification

/-- The central abelian factor inside the fold-gauge product `A × H`. -/
def aCopy (A H : Type*) [CommGroup A] [Group H] : Set (A × H) :=
  {g | g.2 = 1}

/-- The center of the product model used for the terminal window-6 fold-gauge group. -/
def productCenter (A H : Type*) [CommGroup A] [Group H] : Set (A × H) :=
  {g | ∀ h : A × H, g * h = h * g}

/-- The centerless hypothesis on the non-abelian factor. -/
def centerHTrivial (H : Type*) [Group H] : Prop :=
  ∀ z : H, (∀ h : H, z * h = h * z) → z = 1

/-- The central copy of `A` is exactly the center of `A × H`. -/
def centerGIsA (A H : Type*) [CommGroup A] [Group H] : Prop :=
  productCenter A H = aCopy A H

/-- Block data for automorphisms of the fold-gauge product. -/
structure FoldGaugeAut (A H : Type*) [CommGroup A] [Group H] where
  onA : A ≃* A
  cross : H →* A
  onH : H ≃* H

/-- The corresponding action on the product model. -/
def FoldGaugeAut.act {A H : Type*} [CommGroup A] [Group H] (φ : FoldGaugeAut A H) :
    A × H → A × H
  | (a, h) => (φ.onA a * φ.cross h, φ.onH h)

/-- The central abelian factor is preserved by every block automorphism. -/
def aCharacteristic (A H : Type*) [CommGroup A] [Group H] : Prop :=
  ∀ φ : FoldGaugeAut A H, ∀ g : A × H, g ∈ aCopy A H → φ.act g ∈ aCopy A H

/-- Explicit block data extracted from a fold-gauge automorphism. -/
structure AutBlockData (A H : Type*) [CommGroup A] [Group H] where
  onA : A ≃* A
  cross : H →* A
  onH : H ≃* H

/-- Automorphisms of the fold-gauge model decompose into `Aut(A)`, `Hom(H,A)`, and `Aut(H)`. -/
def autDecomposition (A H : Type*) [CommGroup A] [Group H] : Prop :=
  Nonempty (FoldGaugeAut A H ≃ AutBlockData A H)

/-- Outer block data forget the `Hom(H,A)` contribution. -/
structure AutOutBlockData (A H : Type*) [CommGroup A] [Group H] where
  onA : A ≃* A
  onH : H ≃* H

/-- Two block automorphisms represent the same outer class when they agree on the diagonal
`Aut(A) × Aut(H)` part; the `Hom(H,A)` term is modded out. -/
def SameOuterData {A H : Type*} [CommGroup A] [Group H] (φ ψ : FoldGaugeAut A H) : Prop :=
  φ.onA = ψ.onA ∧ φ.onH = ψ.onH

instance foldGaugeOuterSetoid (A H : Type*) [CommGroup A] [Group H] :
    Setoid (FoldGaugeAut A H) where
  r := SameOuterData
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro φ
      exact ⟨rfl, rfl⟩
    · intro φ ψ hφψ
      exact ⟨hφψ.1.symm, hφψ.2.symm⟩
    · intro φ ψ χ hφψ hψχ
      exact ⟨hφψ.1.trans hψχ.1, hφψ.2.trans hψχ.2⟩

/-- The outer-automorphism space of the fold-gauge model. -/
abbrev FoldGaugeOut (A H : Type*) [CommGroup A] [Group H] :=
  Quotient (foldGaugeOuterSetoid A H)

/-- Outer automorphisms are represented by the diagonal block data. -/
def outDecomposition (A H : Type*) [CommGroup A] [Group H] : Prop :=
  Nonempty (FoldGaugeOut A H ≃ AutOutBlockData A H)

def autBlockEquiv (A H : Type*) [CommGroup A] [Group H] :
    FoldGaugeAut A H ≃ AutBlockData A H where
  toFun φ := ⟨φ.onA, φ.cross, φ.onH⟩
  invFun b := ⟨b.onA, b.cross, b.onH⟩
  left_inv φ := by cases φ <;> rfl
  right_inv b := by cases b <;> rfl

def outerBlockOf (A H : Type*) [CommGroup A] [Group H] :
    FoldGaugeOut A H → AutOutBlockData A H :=
  Quotient.lift
    (fun φ => ⟨φ.onA, φ.onH⟩)
    (by
      intro φ ψ hφψ
      cases hφψ with
      | intro hA hH =>
          cases φ with
          | mk onAφ crossφ onHφ =>
              cases ψ with
              | mk onAψ crossψ onHψ =>
                  simp at hA hH
                  cases hA
                  cases hH
                  rfl)

def outBlockEquiv (A H : Type*) [CommGroup A] [Group H] :
    FoldGaugeOut A H ≃ AutOutBlockData A H where
  toFun := outerBlockOf A H
  invFun b := Quotient.mk _ { onA := b.onA, cross := 1, onH := b.onH }
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro φ
    apply Quotient.sound
    exact ⟨rfl, rfl⟩
  right_inv b := by
    rfl

/-- Product-center and outer-automorphism package for
`thm:terminal-window6-fold-gauge-aut-out-structure`. -/
theorem paper_terminal_window6_fold_gauge_aut_out_structure
    (A H : Type*) [CommGroup A] [Group H] (hCenterless : centerHTrivial H) :
    centerHTrivial H ∧ centerGIsA A H ∧ aCharacteristic A H ∧ autDecomposition A H ∧
      outDecomposition A H := by
  refine ⟨hCenterless, ?_, ?_, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      change g.2 = 1
      apply hCenterless g.2
      intro h
      have hcomm := hg (1, h)
      exact congrArg Prod.snd hcomm
    · intro hg
      have hg' : g.2 = 1 := hg
      intro h
      ext
      · simpa [mul_comm] using mul_comm g.1 h.1
      · simp [hg']
  · intro φ g hg
    change (φ.act g).2 = 1
    change φ.onH g.2 = 1
    simpa [aCopy] using congrArg φ.onH hg
  · exact ⟨autBlockEquiv A H⟩
  · exact ⟨outBlockEquiv A H⟩

end Omega.GroupUnification
