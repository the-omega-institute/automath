import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.Algebra.Group.ULift
import Mathlib.Tactic

namespace Omega.Zeta

open scoped Classical

/-- Paper label: `thm:xi-time-part60acb-constant-fiber-free-group-action-criterion`. -/
theorem paper_xi_time_part60acb_constant_fiber_free_group_action_criterion {X Y : Type*}
    [Fintype X] [Fintype Y] (f : Y → X) (hf : Function.Surjective f) :
    (∃ (G : Type*) (_ : Group G) (_ : Fintype G) (_ : MulAction G Y),
        (∀ {g : G}, (∃ y : Y, g • y = y) → g = 1) ∧
          ∀ y y' : Y, ((∃ g : G, g • y = y') ↔ f y = f y')) ↔
      ∃ D : ℕ, 0 < D ∧ ∀ x : X, Fintype.card {y : Y // f y = x} = D := by
  constructor
  · rintro ⟨G, hGroup, hFintype, hAction, hfree, horbit⟩
    letI : Group G := hGroup
    letI : Fintype G := hFintype
    letI : MulAction G Y := hAction
    refine ⟨Fintype.card G, ?_, ?_⟩
    · exact Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
    · intro x
      obtain ⟨y₀, hy₀⟩ := hf x
      let e : G ≃ {y : Y // f y = x} :=
        Equiv.ofBijective
          (fun g : G => ⟨g • y₀, by
            have hsame : f y₀ = f (g • y₀) := (horbit y₀ (g • y₀)).mp ⟨g, rfl⟩
            exact hsame ▸ hy₀⟩)
          (by
            constructor
            · intro g h hgh
              have hfix : (h⁻¹ * g) • y₀ = y₀ := by
                have hval : g • y₀ = h • y₀ := congrArg Subtype.val hgh
                calc
                  (h⁻¹ * g) • y₀ = h⁻¹ • g • y₀ := by simp [mul_smul]
                  _ = h⁻¹ • h • y₀ := by rw [hval]
                  _ = y₀ := by simp
              have hid : h⁻¹ * g = 1 := hfree ⟨y₀, hfix⟩
              have := congrArg (fun a : G => h * a) hid
              simpa [mul_assoc] using this
            · intro z
              obtain ⟨g, hg⟩ := (horbit y₀ z).mpr (by simpa [hy₀] using z.property.symm)
              exact ⟨g, Subtype.ext hg⟩)
      exact (Fintype.card_congr e).symm
  · rintro ⟨D, hDpos, hcard⟩
    letI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
    let G := Multiplicative (ZMod D)
    letI : Fintype G := Fintype.ofEquiv (ZMod D) Multiplicative.ofAdd
    have hGcard : Fintype.card G = D := by
      change @Fintype.card (Multiplicative (ZMod D))
          (Fintype.ofEquiv (ZMod D) Multiplicative.ofAdd) = D
      rw [Fintype.ofEquiv_card, ZMod.card]
    let e : ∀ x : X, {y : Y // f y = x} ≃ G := fun x =>
      Fintype.equivOfCardEq (by
        rw [hcard x]
        exact hGcard.symm)
    let β := Sigma fun x : X => {y : Y // f y = x}
    let E : Y ≃ β :=
      { toFun := fun y => ⟨f y, ⟨y, rfl⟩⟩
        invFun := fun p => p.2.1
        left_inv := by
          intro y
          rfl
        right_inv := by
          rintro ⟨x, y, hy⟩
          cases hy
          rfl }
    letI : MulAction G β :=
      { smul g p := ⟨p.1, (e p.1).symm (g * e p.1 p.2)⟩
        one_smul := by
          rintro ⟨x, y⟩
          change (⟨x, (e x).symm (1 * e x y)⟩ : β) = ⟨x, y⟩
          simp
        mul_smul := by
          intro g h p
          cases p with
          | mk x y =>
            change (⟨x, (e x).symm ((g * h) * e x y)⟩ : β) =
              ⟨x, (e x).symm (g * e x ((e x).symm (h * e x y)) )⟩
            simp [mul_assoc] }
    letI : MulAction G Y := E.mulAction G
    letI : Fintype (ULift G) := Fintype.ofEquiv G Equiv.ulift.symm
    letI : MulAction (ULift G) Y :=
      { smul g y := g.down • y
        one_smul := by
          intro y
          change (1 : G) • y = y
          simp
        mul_smul := by
          intro g h y
          change (g.down * h.down : G) • y = g.down • h.down • y
          simp [mul_smul] }
    refine ⟨ULift G, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · intro g hfix
      obtain ⟨y, hy⟩ := hfix
      have hβ : g.down • E y = E y := by
        simpa [Equiv.smul_def] using congrArg E hy
      cases hEy : E y with
      | mk x z =>
        rw [hEy] at hβ
        change (⟨x, (e x).symm (g.down * e x z)⟩ : β) = ⟨x, z⟩ at hβ
        have hz : (e x).symm (g.down * e x z) = z := by
          exact eq_of_heq (Sigma.mk.inj hβ).2
        have hg : g.down * e x z = e x z := by
          simpa using congrArg (e x) hz
        have := congrArg (fun a : G => a * (e x z)⁻¹) hg
        have hdown : g.down = 1 := by
          simpa [mul_assoc] using this
        exact Equiv.ulift.injective hdown
    · intro y y'
      constructor
      · rintro ⟨g, hg⟩
        have hβ : g.down • E y = E y' := by
          simpa [Equiv.smul_def] using congrArg E hg
        simpa [E] using congrArg Sigma.fst hβ
      · intro hyy'
        let z' : {t : Y // f t = f y} := ⟨y', hyy'.symm⟩
        let g : G := e (f y) z' * (e (f y) ⟨y, rfl⟩)⁻¹
        refine ⟨ULift.up g, ?_⟩
        apply E.injective
        have hEy' : E y' = (⟨f y, z'⟩ : β) := by
          ext <;> simp [E, z', hyy']
        rw [hEy']
        change E ((g : G) • y) = (⟨f y, z'⟩ : β)
        rw [show E ((g : G) • y) = g • E y by simp [Equiv.smul_def]]
        change (⟨f y, (e (f y)).symm (g * e (f y) ⟨y, rfl⟩)⟩ : β) = ⟨f y, z'⟩
        have hsnd : (e (f y)).symm (g * e (f y) ⟨y, rfl⟩) = z' := by
          apply (e (f y)).injective
          rw [(e (f y)).apply_symm_apply]
          dsimp [g]
          rw [mul_assoc, inv_mul_cancel, mul_one]
        exact Sigma.ext rfl (heq_of_eq hsnd)

end Omega.Zeta
