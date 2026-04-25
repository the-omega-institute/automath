import Mathlib.Tactic

namespace Omega.POM

/-- The `q` labelled copies of the lifted state space `Q × G`. -/
abbrev qFoldLiftState (q : ℕ) (Q G : Type*) :=
  Fin q → (Q × G)

/-- The same data reorganized as a `q`-tuple of base states together with a `q`-tuple of group
coordinates. -/
abbrev qFoldMomentLiftState (q : ℕ) (Q G : Type*) :=
  (Fin q → Q) × (Fin q → G)

/-- The canonical Beck--Chevalley witness `(Q × G)^q ≃ Q^q × G^q`. -/
def qFoldLiftEquiv (q : ℕ) (Q G : Type*) :
    qFoldLiftState q Q G ≃ qFoldMomentLiftState q Q G where
  toFun s := (fun i => (s i).1, fun i => (s i).2)
  invFun t := fun i => (t.1 i, t.2 i)
  left_inv s := by
    funext i
    cases h : s i with
    | mk q g =>
        simp [h]
  right_inv t := by
    cases t
    rfl

/-- The `q`-fold moment constraint only reads the visible `Q`-outputs. -/
def qFoldOutputEqual {q : ℕ} {Q Y : Type*} (out : Q → Y) (s : Fin q → Q) : Prop :=
  ∀ i j, out (s i) = out (s j)

/-- The same constraint on the lifted state space, where the group coordinates are ignored. -/
def qFoldLiftOutputEqual {q : ℕ} {Q G Y : Type*} (out : Q → Y)
    (s : qFoldLiftState q Q G) : Prop :=
  ∀ i j, out (s i).1 = out (s j).1

/-- Transporting the lifted relation across the canonical equivalence does not change the
output-equality predicate. -/
theorem qFoldLiftOutputEqual_iff {q : ℕ} {Q G Y : Type*} (out : Q → Y)
    (s : qFoldLiftState q Q G) :
    qFoldLiftOutputEqual out s ↔ qFoldOutputEqual out (qFoldLiftEquiv q Q G s).1 := by
  rfl

/-- Paper label: `prop:pom-mom-lift-beck-chevalley`.
The `q`-fold moment compilation and the lift commute through the canonical witness
`(Q × G)^q ≃ Q^q × G^q`, and the moment-output equality relation is preserved verbatim. -/
theorem paper_pom_mom_lift_beck_chevalley {Q G Y : Type*} [Group G] [Fintype G]
    (q : ℕ) (out : Q → Y) :
    ∃ e : qFoldLiftState q Q G ≃ qFoldMomentLiftState q Q G,
      ∀ s, qFoldLiftOutputEqual out s ↔ qFoldOutputEqual out (e s).1 := by
  refine ⟨qFoldLiftEquiv q Q G, ?_⟩
  intro s
  exact qFoldLiftOutputEqual_iff out s

/-- Paper label: `prop:pom-rmoml-sound`.
The finite abelian RMOML reading is the abelian specialization of the moment--lift
Beck--Chevalley witness. -/
theorem paper_pom_rmoml_sound {Q G Y : Type*} [CommGroup G] [Fintype G] (q : ℕ)
    (out : Q → Y) :
    ∃ e : qFoldLiftState q Q G ≃ qFoldMomentLiftState q Q G,
      ∀ s, qFoldLiftOutputEqual out s ↔ qFoldOutputEqual out (e s).1 := by
  exact paper_pom_mom_lift_beck_chevalley q out

end Omega.POM
