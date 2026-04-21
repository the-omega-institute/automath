import Omega.Folding.KilloNaturalExtensionBranchRegister

namespace Omega.Zeta

/-- The `n`-periodic points of a self-map. -/
def XiPeriodicPoints {X : Type*} (f : X → X) (n : ℕ) :=
  { x : X // (f^[n]) x = x }

/-- Equality of all periodic-point types is the concrete zeta-preservation package used here. -/
def xiPeriodicOrbitZetaPreserving {X Y : Type*} (f : X → X) (g : Y → Y) : Prop :=
  ∀ n : ℕ, Nonempty (XiPeriodicPoints f n ≃ XiPeriodicPoints g n)

/-- The canonical predecessor history attached to an invertible system. -/
def xiNaturalExtensionHistory {X : Type*} (e : X ≃ X) (x : X) : ℕ → X
  | 0 => x
  | n + 1 => e.symm (xiNaturalExtensionHistory e x n)

/-- Realize an invertible system as its natural extension by recursively adjoining predecessors. -/
def xiNaturalExtensionPoint {X : Type*} (e : X ≃ X) (x : X) :
    Omega.Folding.NaturalExtension e.toFun :=
  ⟨xiNaturalExtensionHistory e x, by
    intro n
    simp [xiNaturalExtensionHistory]⟩

/-- For an invertible map, a natural-extension history is uniquely determined by its zeroth
coordinate. -/
def xiNaturalExtensionBaseEquiv {X : Type*} (e : X ≃ X) :
    Omega.Folding.NaturalExtension e.toFun ≃ X where
  toFun s := s.1 0
  invFun := xiNaturalExtensionPoint e
  left_inv s := by
    apply Subtype.ext
    funext n
    induction n with
    | zero =>
        rfl
    | succ n ihn =>
        have hs : s.1 (n + 1) = e.symm (s.1 n) := by
          simpa using congrArg e.symm (s.2 n)
        calc
          xiNaturalExtensionHistory e (s.1 0) (n + 1)
              = e.symm (xiNaturalExtensionHistory e (s.1 0) n) := by
                  rfl
          _ = e.symm (s.1 n) := by
                  simpa [xiNaturalExtensionPoint] using congrArg e.symm ihn
          _ = s.1 (n + 1) := by
                  rw [hs]
  right_inv x := rfl

@[simp] theorem xiNaturalExtensionBaseEquiv_shift {X : Type*} (e : X ≃ X)
    (s : Omega.Folding.NaturalExtension e.toFun) :
    xiNaturalExtensionBaseEquiv e (Omega.Folding.naturalExtensionShift e.toFun s) =
      e (xiNaturalExtensionBaseEquiv e s) :=
  rfl

theorem xiConjIterate {X Y : Type*} (e : X ≃ Y) {f : X → X} {g : Y → Y}
    (h : ∀ x, e (f x) = g (e x)) :
    ∀ n : ℕ, ∀ x : X, e ((f^[n]) x) = (g^[n]) (e x)
  | 0, x => rfl
  | n + 1, x => by
      simp [Function.iterate_succ_apply, h, xiConjIterate e h n]

theorem xiConjSymm {X Y : Type*} (e : X ≃ Y) {f : X → X} {g : Y → Y}
    (h : ∀ x, e (f x) = g (e x)) :
    ∀ y : Y, e.symm (g y) = f (e.symm y) := by
  intro y
  simpa using (congrArg e.symm (h (e.symm y))).symm

/-- Conjugate systems have equivalent periodic-point types at every period. -/
def xiPeriodicPointsEquivOfConj {X Y : Type*} (e : X ≃ Y) {f : X → X} {g : Y → Y}
    (h : ∀ x, e (f x) = g (e x)) (n : ℕ) :
    XiPeriodicPoints f n ≃ XiPeriodicPoints g n where
  toFun x := by
    refine ⟨e x.1, ?_⟩
    calc
      (g^[n]) (e x.1) = e ((f^[n]) x.1) := by
        symm
        exact xiConjIterate e h n x.1
      _ = e x.1 := by
        rw [x.2]
  invFun y := by
    refine ⟨e.symm y.1, ?_⟩
    calc
      (f^[n]) (e.symm y.1) = e.symm ((g^[n]) y.1) := by
        symm
        exact xiConjIterate e.symm (xiConjSymm e h) n y.1
      _ = e.symm y.1 := by
        rw [y.2]
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- For an invertible system, the natural extension is conjugate to the base system, so every
periodic-point set is preserved and the Artin--Mazur zeta data agrees period-by-period.
    thm:xi-natural-extension-periodic-orbit-zeta-preservation -/
theorem paper_xi_natural_extension_periodic_orbit_zeta_preservation {X : Type*} (e : X ≃ X) :
    Nonempty (Omega.Folding.NaturalExtension e.toFun ≃ X) ∧
      xiPeriodicOrbitZetaPreserving (Omega.Folding.naturalExtensionShift e.toFun) e.toFun := by
  refine ⟨⟨xiNaturalExtensionBaseEquiv e⟩, ?_⟩
  intro n
  exact ⟨xiPeriodicPointsEquivOfConj (xiNaturalExtensionBaseEquiv e)
    (xiNaturalExtensionBaseEquiv_shift e) n⟩

end Omega.Zeta
