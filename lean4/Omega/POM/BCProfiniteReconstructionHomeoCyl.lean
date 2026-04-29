import Mathlib.Tactic

namespace Omega.POM

/-- Concrete prefixed finite-cylinder data for the BC profinite reconstruction statement.  A point
of the limiting cylinder space is a compatible family of finite cylinders. -/
structure pom_bc_profinite_reconstruction_homeo_cyl_data where
  Cyl : ℕ → Type*
  G : ℕ → Type*
  cylinderPrefix : ∀ m : ℕ, Cyl (m + 1) → Cyl m
  levelProjection : ∀ m : ℕ, G (m + 1) → G m
  cylinderAction : ∀ m : ℕ, G m → Equiv.Perm (Cyl m)
  action_compatible :
    ∀ m : ℕ, ∀ g : G (m + 1), ∀ c : Cyl (m + 1),
      cylinderPrefix m ((cylinderAction (m + 1) g) c) =
        (cylinderAction m (levelProjection m g)) (cylinderPrefix m c)
  point_exists : ∀ m : ℕ, ∀ c : Cyl m, ∃ x : ∀ n : ℕ, Cyl n,
    (∀ n : ℕ, cylinderPrefix n (x (n + 1)) = x n) ∧ x m = c
  action_faithful :
    ∀ m : ℕ, ∀ g h : G m,
      (∀ c : Cyl m, cylinderAction m g c = cylinderAction m h c) → g = h

/-- The inverse-limit cylinder space. -/
def pom_bc_profinite_reconstruction_homeo_cyl_point
    (D : pom_bc_profinite_reconstruction_homeo_cyl_data) : Type* :=
  { x : ∀ m : ℕ, D.Cyl m // ∀ m : ℕ, D.cylinderPrefix m (x (m + 1)) = x m }

/-- The inverse-limit group-like family of compatible finite actions. -/
def pom_bc_profinite_reconstruction_homeo_cyl_limit
    (D : pom_bc_profinite_reconstruction_homeo_cyl_data) : Type* :=
  { g : ∀ m : ℕ, D.G m // ∀ m : ℕ, D.levelProjection m (g (m + 1)) = g m }

/-- Cylinder-preserving permutations are exactly those induced levelwise by a compatible family. -/
def pom_bc_profinite_reconstruction_homeo_cyl_preserves_cylinders
    (D : pom_bc_profinite_reconstruction_homeo_cyl_data)
    (h : Equiv.Perm (pom_bc_profinite_reconstruction_homeo_cyl_point D)) : Prop :=
  ∃ g : ∀ m : ℕ, D.G m, (∀ m : ℕ, D.levelProjection m (g (m + 1)) = g m) ∧
    ∀ x : pom_bc_profinite_reconstruction_homeo_cyl_point D, ∀ m : ℕ,
      (h x).1 m = D.cylinderAction m (g m) (x.1 m)

/-- The formal statement: the inverse-limit action is faithful and its range is precisely the
cylinder-preserving permutations induced by compatible finite-level actions. -/
def pom_bc_profinite_reconstruction_homeo_cyl_statement
    (D : pom_bc_profinite_reconstruction_homeo_cyl_data) : Prop :=
  ∃ iota :
      pom_bc_profinite_reconstruction_homeo_cyl_limit D →
        Equiv.Perm (pom_bc_profinite_reconstruction_homeo_cyl_point D),
    Function.Injective iota ∧
      Set.range iota =
        {h | pom_bc_profinite_reconstruction_homeo_cyl_preserves_cylinders D h}

/-- The inverse-limit action on compatible cylinder points. -/
def pom_bc_profinite_reconstruction_homeo_cyl_iota
    (D : pom_bc_profinite_reconstruction_homeo_cyl_data)
    (g : pom_bc_profinite_reconstruction_homeo_cyl_limit D) :
    Equiv.Perm (pom_bc_profinite_reconstruction_homeo_cyl_point D) where
  toFun x :=
    ⟨fun m => D.cylinderAction m (g.1 m) (x.1 m), by
      intro m
      calc
        D.cylinderPrefix m (D.cylinderAction (m + 1) (g.1 (m + 1)) (x.1 (m + 1))) =
            D.cylinderAction m (D.levelProjection m (g.1 (m + 1)))
              (D.cylinderPrefix m (x.1 (m + 1))) :=
          D.action_compatible m (g.1 (m + 1)) (x.1 (m + 1))
        _ = D.cylinderAction m (g.1 m) (x.1 m) := by rw [g.2 m, x.2 m]⟩
  invFun x :=
    ⟨fun m => (D.cylinderAction m (g.1 m)).symm (x.1 m), by
      intro m
      apply (D.cylinderAction m (g.1 m)).injective
      have h :=
        D.action_compatible m (g.1 (m + 1))
          ((D.cylinderAction (m + 1) (g.1 (m + 1))).symm (x.1 (m + 1)))
      calc
        D.cylinderAction m (g.1 m)
            (D.cylinderPrefix m
              ((D.cylinderAction (m + 1) (g.1 (m + 1))).symm (x.1 (m + 1)))) =
            D.cylinderAction m (D.levelProjection m (g.1 (m + 1)))
              (D.cylinderPrefix m
                ((D.cylinderAction (m + 1) (g.1 (m + 1))).symm (x.1 (m + 1)))) := by
          rw [g.2 m]
        _ = D.cylinderPrefix m (x.1 (m + 1)) := by simpa using h.symm
        _ = x.1 m := x.2 m
        _ = D.cylinderAction m (g.1 m)
            ((D.cylinderAction m (g.1 m)).symm (x.1 m)) := by simp⟩
  left_inv x := by
    apply Subtype.ext
    funext m
    simp
  right_inv x := by
    apply Subtype.ext
    funext m
    simp

/-- Paper label: `thm:pom-bc-profinite-reconstruction-homeo-cyl`. The compatible finite cylinder
actions assemble to a faithful inverse-limit action, and cylinder extensionality characterizes the
image. -/
theorem paper_pom_bc_profinite_reconstruction_homeo_cyl
    (D : pom_bc_profinite_reconstruction_homeo_cyl_data) :
    pom_bc_profinite_reconstruction_homeo_cyl_statement D := by
  let iotaFun :
      pom_bc_profinite_reconstruction_homeo_cyl_limit D →
        Equiv.Perm (pom_bc_profinite_reconstruction_homeo_cyl_point D) :=
    fun g => pom_bc_profinite_reconstruction_homeo_cyl_iota D g
  refine ⟨iotaFun, ?_, ?_⟩
  · intro g h hgh
    apply Subtype.ext
    funext m
    apply D.action_faithful m
    intro c
    obtain ⟨x, hx, hxm⟩ := D.point_exists m c
    let xlim : pom_bc_profinite_reconstruction_homeo_cyl_point D := ⟨x, hx⟩
    have hcoord := congrArg (fun e : Equiv.Perm
        (pom_bc_profinite_reconstruction_homeo_cyl_point D) => (e xlim).1 m) hgh
    simpa [iotaFun, pom_bc_profinite_reconstruction_homeo_cyl_iota, xlim, hxm] using hcoord
  · ext h
    constructor
    · intro hh
      rcases hh with ⟨g, rfl⟩
      exact ⟨g.1, g.2, by intro x m; rfl⟩
    · intro hh
      rcases hh with ⟨g, hg, haction⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      ext x
      apply Subtype.ext
      funext m
      exact (haction x m).symm

end Omega.POM
