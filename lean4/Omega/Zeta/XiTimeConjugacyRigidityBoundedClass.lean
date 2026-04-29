import Mathlib.Tactic

namespace Omega

/-- Sum of edge labels along a finite vertex path. -/
def xi_time_conjugacy_rigidity_bounded_class_pathSum {V : Type}
    (ell : V → V → ℤ) : List V → ℤ
  | [] => 0
  | [_] => 0
  | v :: w :: path =>
      ell v w + xi_time_conjugacy_rigidity_bounded_class_pathSum ell (w :: path)

/-- Boundary contribution of a potential along a finite vertex path. -/
def xi_time_conjugacy_rigidity_bounded_class_boundary {V : Type}
    (b : V → ℤ) : List V → ℤ
  | [] => 0
  | [_] => 0
  | v :: w :: path =>
      (b w - b v) + xi_time_conjugacy_rigidity_bounded_class_boundary b (w :: path)

/-- Paper label: `thm:xi-time-conjugacy-rigidity-bounded-class`. -/
theorem paper_xi_time_conjugacy_rigidity_bounded_class {V : Type} [Fintype V] [DecidableEq V]
    (ell ell' : V → V → ℤ) (b : V → ℤ) (path : List V)
    (hcoh : ∀ v w, ell' v w = ell v w + b w - b v) :
    xi_time_conjugacy_rigidity_bounded_class_pathSum ell' path =
      xi_time_conjugacy_rigidity_bounded_class_pathSum ell path +
        xi_time_conjugacy_rigidity_bounded_class_boundary b path := by
  induction path with
  | nil =>
      simp [xi_time_conjugacy_rigidity_bounded_class_pathSum,
        xi_time_conjugacy_rigidity_bounded_class_boundary]
  | cons v path ih =>
      cases path with
      | nil =>
          simp [xi_time_conjugacy_rigidity_bounded_class_pathSum,
            xi_time_conjugacy_rigidity_bounded_class_boundary]
      | cons w path =>
          simp [xi_time_conjugacy_rigidity_bounded_class_pathSum,
            xi_time_conjugacy_rigidity_bounded_class_boundary, hcoh, ih]
          ring

end Omega
