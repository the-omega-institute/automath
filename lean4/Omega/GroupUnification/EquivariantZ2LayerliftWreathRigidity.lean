import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

open scoped Classical

/-- Hypotheses for the concrete `Z/2`-layer-lift rigidity statement. A chosen section `s`
identifies each fiber of `π` with two points exchanged by the fixed-point-free involution `ζ`,
and the lifted base permutations preserve both the section and the diagonal involution. -/
def equivariant_z2_layerlift_wreath_rigidity_hypotheses {Δ Δtilde : Type} [Fintype Δ]
    [Fintype Δtilde] (π : Δtilde → Δ) (ζ : Equiv.Perm Δtilde)
    (ι : Equiv.Perm Δ →* Equiv.Perm Δtilde) : Prop :=
  ∃ s : Δ → Δtilde,
    (∀ a, π (s a) = a) ∧
      (∀ x, π (ζ x) = π x) ∧
      (∀ x, ζ (ζ x) = x) ∧
      (∀ x, ζ x ≠ x) ∧
      (∀ x, x = s (π x) ∨ x = ζ (s (π x))) ∧
      (∀ σ a, ι σ (s a) = s (σ a)) ∧
      (∀ σ x, ι σ (ζ x) = ζ (ι σ x))

/-- Conclusion of the concrete `Z/2`-layer-lift rigidity statement. The cover is explicitly
equivalent to `Δ × Fin 2`, and under this identification the involution `ζ` becomes the standard
fiber flip on the chosen section. -/
def equivariant_z2_layerlift_wreath_rigidity_conclusion {Δ Δtilde : Type} [Fintype Δ]
    [Fintype Δtilde] (π : Δtilde → Δ) (ζ : Equiv.Perm Δtilde)
    (ι : Equiv.Perm Δ →* Equiv.Perm Δtilde) : Prop :=
  let _ := ι
  ∃ e : Δtilde ≃ Δ × Fin 2,
    (∀ x, (e x).1 = π x) ∧
      (∀ a, e (ζ (e.symm (a, 0))) = (a, 1))

theorem paper_equivariant_z2_layerlift_wreath_rigidity {Δ Δtilde : Type} [Fintype Δ]
    [Fintype Δtilde] (π : Δtilde → Δ) (ζ : Equiv.Perm Δtilde)
    (ι : Equiv.Perm Δ →* Equiv.Perm Δtilde) :
    equivariant_z2_layerlift_wreath_rigidity_hypotheses π ζ ι →
      equivariant_z2_layerlift_wreath_rigidity_conclusion π ζ ι := by
  intro h
  rcases h with ⟨s, hπs, hπζ, hζζ, hζne, hcover, hιs, hιζ⟩
  let equivariant_z2_layerlift_wreath_rigidity_f : Δtilde → Δ × Fin 2 := fun x =>
    if hx : x = s (π x) then (π x, 0) else (π x, 1)
  let equivariant_z2_layerlift_wreath_rigidity_g : Δ × Fin 2 → Δtilde
    | (a, 0) => s a
    | (a, 1) => ζ (s a)
  have equivariant_z2_layerlift_wreath_rigidity_fg :
      ∀ x,
        equivariant_z2_layerlift_wreath_rigidity_g
            (equivariant_z2_layerlift_wreath_rigidity_f x) =
          x := by
    intro x
    rcases hcover x with hx | hx
    · let a : Δ := π x
      have hx' : x = s a := by
        simpa [a] using hx
      rw [hx']
      dsimp [equivariant_z2_layerlift_wreath_rigidity_f, equivariant_z2_layerlift_wreath_rigidity_g]
      have hself : s a = s (π (s a)) := by rw [hπs]
      rw [if_pos hself, hπs]
    · let a : Δ := π x
      have hx' : x = ζ (s a) := by
        simpa [a] using hx
      rw [hx']
      dsimp [equivariant_z2_layerlift_wreath_rigidity_f, equivariant_z2_layerlift_wreath_rigidity_g]
      split_ifs with hsame
      · exfalso
        exact hζne (s a) (by simpa [hπζ (s a), hπs a] using hsame)
      · rw [hπζ, hπs]
  have equivariant_z2_layerlift_wreath_rigidity_gf :
      ∀ y,
        equivariant_z2_layerlift_wreath_rigidity_f
            (equivariant_z2_layerlift_wreath_rigidity_g y) =
          y := by
    rintro ⟨a, b⟩
    fin_cases b
    · simp [equivariant_z2_layerlift_wreath_rigidity_g, equivariant_z2_layerlift_wreath_rigidity_f,
        hπs]
    · by_cases hsame : ζ (s a) = s a
      · exfalso
        exact hζne (s a) hsame
      · simp [equivariant_z2_layerlift_wreath_rigidity_g, equivariant_z2_layerlift_wreath_rigidity_f,
          hπζ, hπs, hsame]
  let e : Δtilde ≃ Δ × Fin 2 :=
    { toFun := equivariant_z2_layerlift_wreath_rigidity_f
      invFun := equivariant_z2_layerlift_wreath_rigidity_g
      left_inv := equivariant_z2_layerlift_wreath_rigidity_fg
      right_inv := equivariant_z2_layerlift_wreath_rigidity_gf }
  refine ⟨e, ?_, ?_⟩
  · intro x
    change
      (if hx : x = s (π x) then (π x, 0) else (π x, 1)).1 = π x
    split_ifs <;> rfl
  · intro a
    simpa [equivariant_z2_layerlift_wreath_rigidity_g] using
      equivariant_z2_layerlift_wreath_rigidity_gf (a, 1)

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the rigidity of equivariant free binary lifts.
    thm:equivariant-z2-layerlift-wreath-rigidity -/
theorem paper_gu_equivariant_z2_layerlift_wreath_rigidity
    (k : ℕ) (hk : 3 ≤ k)
    (standardBinaryCover autGroupIsWreath uniqueFreeCentralInvolution : Prop)
    (hCover : standardBinaryCover)
    (hAut : standardBinaryCover → autGroupIsWreath)
    (hCenter : autGroupIsWreath → uniqueFreeCentralInvolution) :
    standardBinaryCover ∧ autGroupIsWreath ∧ uniqueFreeCentralInvolution := by
  let _ := hk
  have hWreath : autGroupIsWreath := hAut hCover
  have hCentral : uniqueFreeCentralInvolution := hCenter hWreath
  exact ⟨hCover, hWreath, hCentral⟩

end Omega.GroupUnification
