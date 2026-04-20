import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

theorem paper_pom_spectrum_cannot_induce_universal_section {Ω X : Type*} [Fintype Ω] [Fintype X]
    [DecidableEq Ω] [DecidableEq X] (d : X → ℕ)
    (hrealize : ∃ F : Ω → X, ∀ x, Fintype.card {ω : Ω // F ω = x} = d x)
    (_hnonempty : ∀ x, 1 ≤ d x) (hX : 2 ≤ Fintype.card X) (hx0 : ∃ x0, 2 ≤ d x0) :
    ¬ ∃ s : X → Ω, ∀ F : Ω → X, (∀ x, Fintype.card {ω : Ω // F ω = x} = d x) →
      Function.RightInverse s F := by
  classical
  intro hs
  rcases hs with ⟨s, hs⟩
  rcases hrealize with ⟨F, hF⟩
  rcases hx0 with ⟨x0, _⟩
  have hx1 : ∃ x1, x1 ≠ x0 := by
    by_contra hx1
    have hall : ∀ x : X, x = x0 := by
      intro x
      by_contra hx
      exact hx1 ⟨x, hx⟩
    have hsub : Subsingleton X := ⟨fun a b => by rw [hall a, hall b]⟩
    have hcard : Fintype.card X ≤ 1 := by
      rw [Fintype.card_le_one_iff_subsingleton]
      exact hsub
    omega
  rcases hx1 with ⟨x1, hx10⟩
  let ω0 := s x0
  let ω1 := s x1
  have hsF : Function.RightInverse s F := hs F hF
  have hω0 : F ω0 = x0 := hsF x0
  have hω1 : F ω1 = x1 := hsF x1
  have hω01 : ω0 ≠ ω1 := by
    intro hEq
    apply hx10
    calc
      x1 = F ω1 := hω1.symm
      _ = F ω0 := by simp [hEq]
      _ = x0 := hω0
  let e : Equiv.Perm Ω := Equiv.swap ω0 ω1
  let F' : Ω → X := fun ω => F (e ω)
  have hcard_swap :
      ∀ x : X, Fintype.card {ω : Ω // F' ω = x} = Fintype.card {ω : Ω // F ω = x} := by
    intro x
    refine Fintype.card_congr
      { toFun := fun w => ⟨e w.1, w.2⟩
        invFun := fun w => ⟨e w.1, by simpa [F', e] using w.2⟩
        left_inv := by
          intro w
          ext
          simp [e]
        right_inv := by
          intro w
          ext
          simp [e] }
  have hF' : ∀ x, Fintype.card {ω : Ω // F' ω = x} = d x := by
    intro x
    rw [hcard_swap x, hF x]
  have hsF' : Function.RightInverse s F' := hs F' hF'
  have hx1' : F' (s x0) = x1 := by
    simpa [F', e, ω0, ω1] using hω1
  have hx0' : F' (s x0) = x0 := hsF' x0
  exact hx10 (hx1'.symm.trans hx0')

end Omega.POM
