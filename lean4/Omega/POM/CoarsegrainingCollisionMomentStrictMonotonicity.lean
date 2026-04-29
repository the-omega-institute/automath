import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

attribute [local instance] Classical.decEq

namespace Omega.POM

/-- Paper label: `prop:pom-coarsegraining-collision-moment-strict-monotonicity`. -/
theorem paper_pom_coarsegraining_collision_moment_strict_monotonicity
    {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    (f : Ω → X) (g : Ω → Y) (π : X → Y) (hπ : ∀ ω, g ω = π (f ω))
    (q : ℕ) (hq : 1 < q) :
    (∑ x : X, Fintype.card {ω : Ω // f ω = x} ^ q) ≤
        (∑ y : Y, Fintype.card {ω : Ω // g ω = y} ^ q) ∧
      ((∃ y : Y,
          1 < Fintype.card {x : X // π x = y ∧
            0 < Fintype.card {ω : Ω // f ω = x}}) →
        (∑ x : X, Fintype.card {ω : Ω // f ω = x} ^ q) <
          (∑ y : Y, Fintype.card {ω : Ω // g ω = y} ^ q)) := by
  classical
  let Fine := Σ x : X, Fin q → {ω : Ω // f ω = x}
  let Coarse := Σ y : Y, Fin q → {ω : Ω // g ω = y}
  let Φ : Fine → Coarse := fun a =>
    ⟨π a.1, fun i => ⟨(a.2 i).1, by
      rw [hπ]
      exact congrArg π (a.2 i).2⟩⟩
  have hΦ_inj : Function.Injective Φ := by
    intro a b hab
    let hi : Fin q := ⟨0, by omega⟩
    have hω : (a.2 hi).1 = (b.2 hi).1 :=
      congrArg (fun c : Coarse => (c.2 hi).1) hab
    have hx : a.1 = b.1 := by
      calc
        a.1 = f (a.2 hi).1 := (a.2 hi).2.symm
        _ = f (b.2 hi).1 := congrArg f hω
        _ = b.1 := (b.2 hi).2
    cases a with
    | mk ax av =>
      cases b with
      | mk bx bv =>
        dsimp at hx hab ⊢
        subst bx
        have hav : av = bv := by
          funext i
          apply Subtype.ext
          exact congrArg (fun c : Coarse => (c.2 i).1) hab
        subst bv
        rfl
  have hsumFine :
      Fintype.card Fine = ∑ x : X, Fintype.card {ω : Ω // f ω = x} ^ q := by
    simp [Fine, Fintype.card_sigma]
  have hsumCoarse :
      Fintype.card Coarse = ∑ y : Y, Fintype.card {ω : Ω // g ω = y} ^ q := by
    simp [Coarse, Fintype.card_sigma]
  constructor
  · rw [← hsumFine, ← hsumCoarse]
    exact Fintype.card_le_of_injective Φ hΦ_inj
  · intro hmerge
    rw [← hsumFine, ← hsumCoarse]
    refine Fintype.card_lt_of_injective_not_surjective Φ hΦ_inj ?_
    rcases hmerge with ⟨y, hy⟩
    obtain ⟨x₁, x₂, hxne⟩ := Fintype.one_lt_card_iff.mp hy
    have hx₁π : π x₁.1 = y := x₁.2.1
    have hx₂π : π x₂.1 = y := x₂.2.1
    have hx₁pos : 0 < Fintype.card {ω : Ω // f ω = x₁.1} := x₁.2.2
    have hx₂pos : 0 < Fintype.card {ω : Ω // f ω = x₂.1} := x₂.2.2
    obtain ⟨ω₁⟩ := Fintype.card_pos_iff.mp hx₁pos
    obtain ⟨ω₂⟩ := Fintype.card_pos_iff.mp hx₂pos
    let i0 : Fin q := ⟨0, by omega⟩
    let i1 : Fin q := ⟨1, hq⟩
    let mixed : Coarse := ⟨y, fun i =>
      if i = i0 then ⟨ω₁.1, by simp [hπ ω₁.1, ω₁.2, hx₁π]⟩
      else ⟨ω₂.1, by simp [hπ ω₂.1, ω₂.2, hx₂π]⟩⟩
    intro hsurj
    rcases hsurj mixed with ⟨a, ha⟩
    have hax₁ : a.1 = x₁.1 := by
      have hω : (a.2 i0).1 = ω₁.1 := by
        simpa [Φ, mixed, i0] using congrArg (fun c : Coarse => (c.2 i0).1) ha
      calc
        a.1 = f (a.2 i0).1 := (a.2 i0).2.symm
        _ = f ω₁.1 := congrArg f hω
        _ = x₁.1 := ω₁.2
    have hax₂ : a.1 = x₂.1 := by
      have hω : (a.2 i1).1 = ω₂.1 := by
        have hneq : i1 ≠ i0 := by
          intro h
          exact one_ne_zero (congrArg Fin.val h)
        simpa [Φ, mixed, i1, hneq] using congrArg (fun c : Coarse => (c.2 i1).1) ha
      calc
        a.1 = f (a.2 i1).1 := (a.2 i1).2.symm
        _ = f ω₂.1 := congrArg f hω
        _ = x₂.1 := ω₂.2
    have : x₁ = x₂ := by
      apply Subtype.ext
      exact hax₁.symm.trans hax₂
    exact hxne this

end Omega.POM
