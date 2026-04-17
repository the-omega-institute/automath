import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- A concrete `48 = 16 · 3` model for the window-6 family carrier. -/
abbrev Window6FamilyCarrier := Fin 16 × Fin 3

/-- The standard three-family projection. -/
def window6FamilyProjection : Window6FamilyCarrier → Fin 3 :=
  Prod.snd

/-- The fiber over a boundary family label. -/
def window6FamilyFiber (i : Fin 3) :=
  {x : Window6FamilyCarrier // window6FamilyProjection x = i}

instance instFintypeWindow6FamilyFiber (i : Fin 3) : Fintype (window6FamilyFiber i) := by
  dsimp [window6FamilyFiber, window6FamilyProjection]
  infer_instance

/-- The `16`-point model for an index-`3` family fiber. -/
abbrev Window6FamilySubgroupModel := Fin 16

/-- Each family fiber is canonically identified with the standard `16`-point model. -/
def window6FamilyFiberEquiv (i : Fin 3) : Window6FamilySubgroupModel ≃ window6FamilyFiber i where
  toFun a := ⟨(a, i), rfl⟩
  invFun x := x.1.1
  left_inv a := rfl
  right_inv x := by
    rcases x with ⟨⟨a, j⟩, hj⟩
    cases hj
    rfl

/-- The projection ignores the `16`-point fiber coordinate. -/
def window6FiberInvariant (π : Window6FamilyCarrier → Fin 3) : Prop :=
  ∀ a b : Fin 16, ∀ i : Fin 3, π (a, i) = π (b, i)

/-- Equivariance with respect to relabeling the three boundary families. -/
def window6BoundaryEquivariant (π : Window6FamilyCarrier → Fin 3) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), ∀ a : Fin 16, ∀ i : Fin 3, π (a, σ i) = σ (π (a, i))

private theorem window6_projection_basepoint
    (π : Window6FamilyCarrier → Fin 3)
    (_hInv : window6FiberInvariant π)
    (hEqv : window6BoundaryEquivariant π) :
    ∀ i : Fin 3, π (0, i) = i := by
  intro i
  fin_cases i
  · let j : Fin 3 := π (0, 0)
    have hfix : j = Equiv.swap (1 : Fin 3) 2 j := by
      simpa [j] using hEqv (Equiv.swap (1 : Fin 3) 2) 0 0
    change π (0, 0) = 0
    have hlt : (π (0, 0)).1 < 3 := (π (0, 0)).2
    interval_cases hval : (π (0, 0)).1
    · apply Fin.ext
      simpa using hval
    · exfalso
      have hπ : π (0, 0) = 1 := by
        apply Fin.ext
        simpa using hval
      have hbad : (1 : Fin 3) = 2 := by
        simpa [j, hπ] using hfix
      have hbadv : (1 : Nat) = 2 := congrArg Fin.val hbad
      omega
    · exfalso
      have hπ : π (0, 0) = 2 := by
        apply Fin.ext
        simpa using hval
      have hbad : (2 : Fin 3) = 1 := by
        simpa [j, hπ] using hfix
      have hbadv : (2 : Nat) = 1 := congrArg Fin.val hbad
      omega
  · let j : Fin 3 := π (0, 1)
    have hfix : j = Equiv.swap (0 : Fin 3) 2 j := by
      simpa [j] using hEqv (Equiv.swap (0 : Fin 3) 2) 0 1
    change π (0, 1) = 1
    have hlt : (π (0, 1)).1 < 3 := (π (0, 1)).2
    interval_cases hval : (π (0, 1)).1
    · exfalso
      have hπ : π (0, 1) = 0 := by
        apply Fin.ext
        simpa using hval
      have hbad : (0 : Fin 3) = 2 := by
        simpa [j, hπ] using hfix
      have hbadv : (0 : Nat) = 2 := congrArg Fin.val hbad
      omega
    · apply Fin.ext
      simpa using hval
    · exfalso
      have hπ : π (0, 1) = 2 := by
        apply Fin.ext
        simpa using hval
      have hbad : (2 : Fin 3) = 0 := by
        simpa [j, hπ] using hfix
      have hbadv : (2 : Nat) = 0 := congrArg Fin.val hbad
      omega
  · let j : Fin 3 := π (0, 2)
    have hfix : j = Equiv.swap (0 : Fin 3) 1 j := by
      simpa [j] using hEqv (Equiv.swap (0 : Fin 3) 1) 0 2
    change π (0, 2) = 2
    have hlt : (π (0, 2)).1 < 3 := (π (0, 2)).2
    interval_cases hval : (π (0, 2)).1
    · exfalso
      have hπ : π (0, 2) = 0 := by
        apply Fin.ext
        simpa using hval
      have hbad : (0 : Fin 3) = 1 := by
        simpa [j, hπ] using hfix
      have hbadv : (0 : Nat) = 1 := congrArg Fin.val hbad
      omega
    · exfalso
      have hπ : π (0, 2) = 1 := by
        apply Fin.ext
        simpa using hval
      have hbad : (1 : Fin 3) = 0 := by
        simpa [j, hπ] using hfix
      have hbadv : (1 : Nat) = 0 := congrArg Fin.val hbad
      omega
    · apply Fin.ext
      simpa using hval

/-- Paper-facing wrapper for the window-6 three-family projection: the `48`-point carrier splits
into three canonical `16`-point fibers, and any projection that is fiber-invariant and equivariant
for the boundary-label `S₃`-action is forced to be the standard quotient map.
    thm:window6-family-projection-wequivariant-uniqueness -/
theorem paper_window6_family_projection_wequivariant_uniqueness :
    Fintype.card Window6FamilyCarrier = 48 ∧
      Fintype.card (Fin 3) = 3 ∧
      (∀ i : Fin 3, Fintype.card (window6FamilyFiber i) = 16) ∧
      (∀ i : Fin 3, Nonempty (Window6FamilySubgroupModel ≃ window6FamilyFiber i)) ∧
      (∀ π : Window6FamilyCarrier → Fin 3,
        window6FiberInvariant π →
          window6BoundaryEquivariant π →
            π = window6FamilyProjection) := by
  refine ⟨by simp [Window6FamilyCarrier], by simp, ?_, ?_, ?_⟩
  · intro i
    simpa using (Fintype.card_congr (window6FamilyFiberEquiv i)).symm
  · intro i
    exact ⟨window6FamilyFiberEquiv i⟩
  · intro π hInv hEqv
    funext x
    rcases x with ⟨a, i⟩
    calc
      π (a, i) = π (0, i) := hInv a 0 i
      _ = i := window6_projection_basepoint π hInv hEqv i
      _ = window6FamilyProjection (a, i) := rfl

end Omega.GU
