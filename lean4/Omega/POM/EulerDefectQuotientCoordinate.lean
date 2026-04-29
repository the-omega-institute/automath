import Mathlib.Tactic

namespace Omega.POM

/-- The two-axis toy Euler-defect model used to package the quotient-coordinate statement. -/
abbrev EulerPoint := Bool × Bool

/-- Scalar-valued functions on the two-axis character cube. -/
abbrev EulerFn := EulerPoint → ℚ

/-- Functions normalized to vanish at the basepoint `(false, false)`. -/
abbrev BasedEulerFn := {f : EulerFn // f (false, false) = 0}

/-- Axis-decomposable functions are sums of singleton-axis components. -/
def AxisDecomposable (f : EulerFn) : Prop :=
  ∃ u v : Bool → ℚ, u false = 0 ∧ v false = 0 ∧ ∀ a b, f (a, b) = u a + v b

/-- The Möbius projection removing the singleton-axis contributions. -/
def eulerProjection (f : EulerFn) : EulerFn := fun x =>
  f x - f (x.1, false) - f (false, x.2) + f (false, false)

/-- Interaction functions vanish on both coordinate axes. -/
def IsInteractionFunction (f : EulerFn) : Prop :=
  (∀ a : Bool, f (a, false) = 0) ∧ ∀ b : Bool, f (false, b) = 0

/-- The interaction subspace. -/
abbrev InteractionFn := {f : EulerFn // IsInteractionFunction f}

lemma axisDecomposable_zero : AxisDecomposable (fun _ => (0 : ℚ)) := by
  refine ⟨fun _ => 0, fun _ => 0, rfl, rfl, ?_⟩
  intro a b
  simp

lemma AxisDecomposable.neg {f : EulerFn} (hf : AxisDecomposable f) :
    AxisDecomposable (fun x => -f x) := by
  rcases hf with ⟨u, v, hu, hv, hrepr⟩
  refine ⟨fun a => -u a, fun b => -v b, by simp [hu], by simp [hv], ?_⟩
  intro a b
  simp [hrepr a b, add_comm]

lemma AxisDecomposable.add {f g : EulerFn} (hf : AxisDecomposable f) (hg : AxisDecomposable g) :
    AxisDecomposable (fun x => f x + g x) := by
  rcases hf with ⟨u₁, v₁, hu₁, hv₁, h₁⟩
  rcases hg with ⟨u₂, v₂, hu₂, hv₂, h₂⟩
  refine ⟨fun a => u₁ a + u₂ a, fun b => v₁ b + v₂ b, by simp [hu₁, hu₂],
    by simp [hv₁, hv₂], ?_⟩
  intro a b
  simp [h₁ a b, h₂ a b, add_left_comm, add_comm]

lemma eulerProjection_sub (f g : EulerFn) :
    eulerProjection (fun x => f x - g x) = fun x => eulerProjection f x - eulerProjection g x := by
  funext x
  rcases x with ⟨a, b⟩
  simp [eulerProjection]
  ring

lemma eulerProjection_axisDecomposable_zero {f : EulerFn} (hf : AxisDecomposable f) :
    eulerProjection f = 0 := by
  rcases hf with ⟨u, v, hu, hv, hrepr⟩
  funext x
  rcases x with ⟨a, b⟩
  simp [eulerProjection, hrepr, hu, hv]

lemma axisDecomposable_iff_projection_eq_zero (f : BasedEulerFn) :
    AxisDecomposable (f : EulerFn) ↔ eulerProjection (f : EulerFn) = 0 := by
  constructor
  · intro hf
    exact eulerProjection_axisDecomposable_zero hf
  · intro hproj
    refine ⟨fun a => f.1 (a, false), fun b => f.1 (false, b), f.2, f.2, ?_⟩
    intro a b
    have h := congrFun hproj (a, b)
    simp [eulerProjection, f.2] at h
    linarith

def canonicalRepresentative (f : BasedEulerFn) : InteractionFn := by
  refine ⟨eulerProjection (f : EulerFn), ?_⟩
  refine ⟨?_, ?_⟩
  · intro a
    simp [eulerProjection]
  · intro b
    simp [eulerProjection]

def interactionToBased (g : InteractionFn) : BasedEulerFn :=
  ⟨g, g.2.1 false⟩

def EulerAxisSetoid : Setoid BasedEulerFn where
  r f g := AxisDecomposable (fun x => f.1 x - g.1 x)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      simpa using axisDecomposable_zero
    · intro f g hfg
      have hneg := AxisDecomposable.neg hfg
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    · intro f g h hfg hgh
      have hadd := AxisDecomposable.add hfg hgh
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

/-- The Euler-defect quotient by the axis-decomposable subspace. -/
abbrev EulerDefectQuotient := Quotient EulerAxisSetoid

lemma projection_respects {f g : BasedEulerFn} (hfg : EulerAxisSetoid.r f g) :
    canonicalRepresentative f = canonicalRepresentative g := by
  apply Subtype.ext
  funext x
  have hzero :
      eulerProjection (fun y => f.1 y - g.1 y) x = 0 := by
    have hz :
        eulerProjection (fun y => f.1 y - g.1 y) = 0 :=
      (axisDecomposable_iff_projection_eq_zero
        ⟨(fun y => f.1 y - g.1 y), by simp [f.2, g.2]⟩).1 hfg
    simpa using congrFun hz x
  have hsub := congrFun (eulerProjection_sub (f : EulerFn) (g : EulerFn)) x
  rw [hsub] at hzero
  exact sub_eq_zero.mp hzero

/-- The quotient-coordinate map into the interaction subspace. -/
def quotientCoordinate : EulerDefectQuotient → InteractionFn :=
  Quotient.lift canonicalRepresentative (by
    intro f g hfg
    exact projection_respects hfg)

/-- The quotient class of an interaction function. -/
def interactionClass (g : InteractionFn) : EulerDefectQuotient :=
  Quotient.mk EulerAxisSetoid (interactionToBased g)

lemma canonicalRepresentative_eq_self (g : InteractionFn) :
    canonicalRepresentative (interactionToBased g) = g := by
  apply Subtype.ext
  funext x
  rcases x with ⟨a, b⟩
  have hleft := g.2.1
  have hright := g.2.2
  cases a <;> cases b <;> simp [canonicalRepresentative, interactionToBased, eulerProjection, hleft,
    hright]

lemma class_eq_canonical (f : BasedEulerFn) :
    interactionClass (canonicalRepresentative f) = Quotient.mk EulerAxisSetoid f := by
  apply Quotient.sound
  refine ⟨fun a => -f.1 (a, false), fun b => -f.1 (false, b), by simp [f.2], by simp [f.2], ?_⟩
  intro a b
  simp [canonicalRepresentative, eulerProjection, interactionToBased, f.2]
  ring_nf

lemma interactionClass_leftInverse :
    Function.LeftInverse interactionClass quotientCoordinate := by
  intro q
  refine Quotient.inductionOn q ?_
  intro f
  simpa [quotientCoordinate] using class_eq_canonical f

lemma quotientCoordinate_rightInverse :
    Function.RightInverse interactionClass quotientCoordinate := by
  intro g
  simp [interactionClass, quotientCoordinate, canonicalRepresentative_eq_self]

lemma quotientCoordinate_bijective : Function.Bijective quotientCoordinate := by
  refine ⟨?_, ?_⟩
  · intro q₁ q₂ hq
    exact interactionClass_leftInverse.injective hq
  · intro g
    exact ⟨interactionClass g, quotientCoordinate_rightInverse g⟩

lemma canonicalRepresentative_unique (f : BasedEulerFn) (g : InteractionFn)
    (hclass : interactionClass g = Quotient.mk EulerAxisSetoid f) :
    g = canonicalRepresentative f := by
  have h := congrArg quotientCoordinate hclass
  simpa [interactionClass, quotientCoordinate, canonicalRepresentative_eq_self] using h

/-- The higher-order Euler anomaly is the Möbius projection onto the interaction subspace: its
kernel is exactly the axis-decomposable functions, it coordinates the quotient by singleton
components, and every quotient class has the unique canonical representative obtained by removing
the singleton-axis parts.
    thm:pom-euler-defect-quotient-coordinate -/
theorem paper_pom_euler_defect_quotient_coordinate :
    (∀ f : BasedEulerFn, AxisDecomposable (f : EulerFn) ↔ eulerProjection (f : EulerFn) = 0) ∧
    Function.Bijective quotientCoordinate ∧
    (∀ f : BasedEulerFn, interactionClass (canonicalRepresentative f) = Quotient.mk EulerAxisSetoid f) ∧
    (∀ f : BasedEulerFn, ∀ g : InteractionFn,
      interactionClass g = Quotient.mk EulerAxisSetoid f → g = canonicalRepresentative f) := by
  refine ⟨axisDecomposable_iff_projection_eq_zero, quotientCoordinate_bijective,
    class_eq_canonical, ?_⟩
  intro f g hclass
  exact canonicalRepresentative_unique f g hclass

end Omega.POM
