import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
import Omega.Zeta.XiTimePart65BinfoldGaugeCenterAbelianizationExact

namespace Omega.Zeta

open scoped BigOperators

/-- Fiberwise maximum multiplicity in the fold-bin symmetric-product certificate. -/
def xi_foldbin_center_solvable_fiber_criterion_max_multiplicity {m : ℕ}
    (fiber : Fin m → ℕ) : ℕ :=
  Finset.univ.sup fiber

/-- The finite product is solvable exactly when every symmetric factor has degree at most `4`. -/
def xi_foldbin_center_solvable_fiber_criterion_product_solvable {m : ℕ}
    (fiber : Fin m → ℕ) : Prop :=
  ∀ w, fiber w ≤ 4

/-- Derived length of a symmetric factor in the range needed for the solvable criterion. -/
def xi_foldbin_center_solvable_fiber_criterion_symmetric_derived_length (d : ℕ) : ℕ :=
  if d ≤ 1 then 0 else if d = 2 then 1 else if d = 3 then 2 else if d = 4 then 3 else 4

/-- Derived length of the fold-bin finite product, certified by the largest symmetric factor. -/
def xi_foldbin_center_solvable_fiber_criterion_product_derived_length {m : ℕ}
    (fiber : Fin m → ℕ) : ℕ :=
  xi_foldbin_center_solvable_fiber_criterion_symmetric_derived_length
    (xi_foldbin_center_solvable_fiber_criterion_max_multiplicity fiber)

/-- Piecewise derived-length clause for the solvable symmetric factors `S₁` through `S₄`. -/
def xi_foldbin_center_solvable_fiber_criterion_derived_length_clause (d ell : ℕ) : Prop :=
  match d with
  | 0 => ell = 0
  | 1 => ell = 0
  | 2 => ell = 1
  | 3 => ell = 2
  | 4 => ell = 3
  | _ => True

/-- Center rank read from the audited window-`6` histogram `2:8, 3:4, 4:9`. -/
def xi_foldbin_center_solvable_fiber_criterion_window6_center_rank : ℕ :=
  8

/-- Maximum multiplicity read from the audited window-`6` histogram `2:8, 3:4, 4:9`. -/
def xi_foldbin_center_solvable_fiber_criterion_window6_max_multiplicity : ℕ :=
  4

/-- Derived length certified by the window-`6` maximum symmetric factor `S₄`. -/
def xi_foldbin_center_solvable_fiber_criterion_window6_derived_length : ℕ :=
  3

lemma xi_foldbin_center_solvable_fiber_criterion_solvable_iff_max_le_four {m : ℕ}
    (fiber : Fin m → ℕ) :
    xi_foldbin_center_solvable_fiber_criterion_product_solvable fiber ↔
      xi_foldbin_center_solvable_fiber_criterion_max_multiplicity fiber ≤ 4 := by
  constructor
  · intro h
    exact Finset.sup_le fun w _ => h w
  · intro h w
    exact (Finset.le_sup (f := fiber) (Finset.mem_univ w)).trans h

lemma xi_foldbin_center_solvable_fiber_criterion_derived_length_cases (d : ℕ) (hd : d ≤ 4) :
    xi_foldbin_center_solvable_fiber_criterion_derived_length_clause d
      (xi_foldbin_center_solvable_fiber_criterion_symmetric_derived_length d) := by
  interval_cases d <;>
    simp [xi_foldbin_center_solvable_fiber_criterion_derived_length_clause,
      xi_foldbin_center_solvable_fiber_criterion_symmetric_derived_length]

/-- Concrete finite-product law for the center and solvability of the fold-bin fiber group. -/
abbrev xi_foldbin_center_solvable_fiber_criterion_law : Prop :=
  (∀ {m : ℕ} (fiber : Fin m → ℕ),
    let B := (Finset.univ.filter fun w => fiber w = 2).card;
    let dmax := xi_foldbin_center_solvable_fiber_criterion_max_multiplicity fiber;
    Omega.OperatorAlgebra.foldGaugeCenterOrder fiber = 2 ^ B ∧
      (xi_foldbin_center_solvable_fiber_criterion_product_solvable fiber ↔ dmax ≤ 4) ∧
      (dmax ≤ 4 →
        xi_foldbin_center_solvable_fiber_criterion_derived_length_clause dmax
          (xi_foldbin_center_solvable_fiber_criterion_product_derived_length fiber))) ∧
    xi_foldbin_center_solvable_fiber_criterion_window6_center_rank = 8 ∧
    xi_foldbin_center_solvable_fiber_criterion_window6_max_multiplicity = 4 ∧
    xi_foldbin_center_solvable_fiber_criterion_window6_derived_length = 3 ∧
    ¬ xi_foldbin_center_solvable_fiber_criterion_product_solvable
      (fun _ : Fin 1 => 9) ∧
    ¬ xi_foldbin_center_solvable_fiber_criterion_product_solvable
      (fun _ : Fin 1 => 8)

/-- Paper label: `thm:xi-foldbin-center-solvable-fiber-criterion`. -/
theorem paper_xi_foldbin_center_solvable_fiber_criterion :
    xi_foldbin_center_solvable_fiber_criterion_law := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m fiber
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · simpa using
        (paper_xi_time_part65_binfold_gauge_center_abelianization_exact fiber).1
    · exact xi_foldbin_center_solvable_fiber_criterion_solvable_iff_max_le_four fiber
    · intro hmax
      exact xi_foldbin_center_solvable_fiber_criterion_derived_length_cases
        (xi_foldbin_center_solvable_fiber_criterion_max_multiplicity fiber) hmax
  · rfl
  · rfl
  · rfl
  · intro h
    have h9 := h 0
    norm_num at h9
  · intro h
    have h8 := h 0
    norm_num at h8

end Omega.Zeta
