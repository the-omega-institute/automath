import Mathlib.Tactic

namespace Omega.Conclusion

/-- Boundary layer with three fibers and two sheets in each fiber. -/
abbrev conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint :=
  Fin 3 × Bool

/-- Canonical sheet flip on each two-point boundary fiber. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint :=
  (p.1, !p.2)

/-- Symmetric boundary functions are constant on each sheet-flip orbit. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ) :
    Prop :=
  ∀ p, f (conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip p) = f p

/-- Antisymmetric boundary functions change sign under the sheet flip. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ) :
    Prop :=
  ∀ p, f (conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip p) = -f p

/-- Pointwise symmetric projection on the boundary layer. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ)
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) : ℚ :=
  (f p + f (conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip p)) / 2

/-- Pointwise antisymmetric projection on the boundary layer. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ)
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) : ℚ :=
  (f p - f (conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip p)) / 2

/-- A symmetric function is determined by one scalar on each of the three boundary fibers. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber
    (g : Fin 3 → ℚ)
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) : ℚ :=
  g p.1

/-- An antisymmetric function is determined by its value on the `false` sheet of each fiber. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber
    (g : Fin 3 → ℚ)
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) : ℚ :=
  if p.2 then -g p.1 else g p.1

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_flip_involutive
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip
        (conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip p) = p := by
  cases p
  simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip]

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart_symmetric
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric
      (conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart f) := by
  intro p
  unfold conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart
  rw [conclusion_window6_boundary_symmetric_antisymmetric_splitting_flip_involutive]
  ring

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart_antisymmetric
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric
      (conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart f) := by
  intro p
  unfold conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart
  rw [conclusion_window6_boundary_symmetric_antisymmetric_splitting_flip_involutive]
  ring

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_pointwise_sum
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ)
    (p : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart f p +
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart f p = f p := by
  unfold conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart
  ring

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetric_from_fiber
    (g : Fin 3 → ℚ) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric
      (conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber g) := by
  intro p
  simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip,
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber]

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetric_reconstruct
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ)
    (hf : conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric f) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber
        (fun i => f (i, false)) = f := by
  funext p
  cases p with
  | mk i b =>
      cases b
      · simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber]
      · have h := hf (i, false)
        simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip,
          conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber] at h ⊢
        exact h.symm

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetric_from_fiber
    (g : Fin 3 → ℚ) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric
      (conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber g) := by
  intro p
  cases p with
  | mk i b =>
      cases b <;>
        simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip,
          conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber]

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetric_reconstruct
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ)
    (hf : conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric f) :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber
        (fun i => f (i, false)) = f := by
  funext p
  cases p with
  | mk i b =>
      cases b
      · simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber]
      · have h := hf (i, false)
        simp [conclusion_window6_boundary_symmetric_antisymmetric_splitting_sheetFlip,
          conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber] at h ⊢
        exact h.symm

lemma conclusion_window6_boundary_symmetric_antisymmetric_splitting_intersection_zero
    (f : conclusion_window6_boundary_symmetric_antisymmetric_splitting_BoundaryPoint → ℚ)
    (hs : conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric f)
    (ha : conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric f) :
    f = 0 := by
  funext p
  have hs' := hs p
  have ha' := ha p
  change f p = (0 : ℚ)
  have hzero : f p = -f p := hs'.symm.trans ha'
  linarith

/-- Concrete boundary-layer statement: every function splits into sheet-constant and sheet-sign
parts; each part has one independent scalar on each of the three two-point fibers, and the
intersection is zero. -/
def conclusion_window6_boundary_symmetric_antisymmetric_splitting_statement : Prop :=
  (∀ f,
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric
        (conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart f) ∧
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric
        (conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart f) ∧
      ∀ p,
        conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart f p +
          conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart f p = f p) ∧
    (∀ g,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric
        (conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber g)) ∧
    (∀ f,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric f →
        conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetricFromFiber
          (fun i => f (i, false)) = f) ∧
    (∀ g,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric
        (conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber g)) ∧
    (∀ f,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric f →
        conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetricFromFiber
          (fun i => f (i, false)) = f) ∧
    (∀ f,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_Symmetric f →
        conclusion_window6_boundary_symmetric_antisymmetric_splitting_Antisymmetric f → f = 0) ∧
    Fintype.card (Fin 3) = 3

/-- Paper label: `thm:conclusion-window6-boundary-symmetric-antisymmetric-splitting`. -/
theorem paper_conclusion_window6_boundary_symmetric_antisymmetric_splitting :
    conclusion_window6_boundary_symmetric_antisymmetric_splitting_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · intro f
    exact ⟨conclusion_window6_boundary_symmetric_antisymmetric_splitting_symPart_symmetric f,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_antiPart_antisymmetric f,
      conclusion_window6_boundary_symmetric_antisymmetric_splitting_pointwise_sum f⟩
  · exact conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetric_from_fiber
  · exact conclusion_window6_boundary_symmetric_antisymmetric_splitting_symmetric_reconstruct
  · exact conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetric_from_fiber
  · exact conclusion_window6_boundary_symmetric_antisymmetric_splitting_antisymmetric_reconstruct
  · exact conclusion_window6_boundary_symmetric_antisymmetric_splitting_intersection_zero

end Omega.Conclusion
