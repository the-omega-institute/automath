import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification.ParryEndpointCollapse

variable {α : Type*}

/-- Product of transition weights along a nonempty word. -/
def transitionWeight (P : α → α → ℝ) : List α → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: t => P a b * transitionWeight P (b :: t)

/-- Cylinder probability built from an initial distribution and transition kernel. -/
def cylinderWeight (π : α → ℝ) (P : α → α → ℝ) : List α → ℝ
  | [] => 0
  | a :: t => π a * transitionWeight P (a :: t)

private theorem transitionWeight_telescope
    (P : α → α → ℝ) (r : α → ℝ) (lam : ℝ)
    (hP : ∀ a b, P a b = r b / (lam * r a))
    (hlam : lam ≠ 0) (hr : ∀ a, r a ≠ 0) :
    ∀ a u,
      transitionWeight P (a :: u) = r (List.getLast (a :: u) (by simp)) / (r a * lam ^ u.length)
  | a, [] => by
      simp [transitionWeight]
      field_simp [hr a]
  | a, b :: t => by
      have ih := transitionWeight_telescope P r lam hP hlam hr b t
      rw [transitionWeight, hP, ih]
      simp
      field_simp [hlam, hr a, hr b]
      rw [pow_succ]
      ring

/-- Paper-facing seed package for Parry endpoint collapse.
    thm:parry-endpoint-collapse -/
theorem paper_parry_endpoint_collapse_seeds
    (π : α → ℝ) (P : α → α → ℝ) (ℓ r : α → ℝ) (lam Z : ℝ)
    (hπ : ∀ a, π a = ℓ a * r a / Z)
    (hP : ∀ a b, P a b = r b / (lam * r a))
    (hlam : lam ≠ 0) (hZ : Z ≠ 0) (hr : ∀ a, r a ≠ 0)
    (a : α) (u : List α) :
    cylinderWeight π P (a :: u) =
      ℓ a * r (List.getLast (a :: u) (by simp)) / (Z * lam ^ u.length) := by
  simp [cylinderWeight, hπ]
  rw [transitionWeight_telescope P r lam hP hlam hr]
  field_simp [hlam, hZ, hr a]

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_parry_endpoint_collapse_package
    (π : α → ℝ) (P : α → α → ℝ) (ℓ r : α → ℝ) (lam Z : ℝ)
    (hπ : ∀ a, π a = ℓ a * r a / Z)
    (hP : ∀ a b, P a b = r b / (lam * r a))
    (hlam : lam ≠ 0) (hZ : Z ≠ 0) (hr : ∀ a, r a ≠ 0)
    (a : α) (u : List α) :
    cylinderWeight π P (a :: u) =
      ℓ a * r (List.getLast (a :: u) (by simp)) / (Z * lam ^ u.length) :=
  paper_parry_endpoint_collapse_seeds π P ℓ r lam Z hπ hP hlam hZ hr a u

/-- Paper wrapper theorem matching the exact publication-facing name.
    thm:parry-endpoint-collapse -/
theorem paper_parry_endpoint_collapse
    (π : α → ℝ) (P : α → α → ℝ) (ℓ r : α → ℝ) (lam Z : ℝ)
    (hπ : ∀ a, π a = ℓ a * r a / Z)
    (hP : ∀ a b, P a b = r b / (lam * r a))
    (hlam : lam ≠ 0) (hZ : Z ≠ 0) (hr : ∀ a, r a ≠ 0)
    (a : α) (u : List α) :
    cylinderWeight π P (a :: u) =
      ℓ a * r (List.getLast (a :: u) (by simp)) / (Z * lam ^ u.length) := by
  simpa using paper_parry_endpoint_collapse_package π P ℓ r lam Z hπ hP hlam hZ hr a u

end Omega.GroupUnification.ParryEndpointCollapse
