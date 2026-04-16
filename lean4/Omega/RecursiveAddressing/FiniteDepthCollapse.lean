import Mathlib.Tactic

namespace Omega.RecursiveAddressing.FiniteDepthCollapse

/-- A one-sided local rule with window length `extra + 1`. -/
abbrev LocalCode (α : Type) := Σ extra : Nat, (Fin (extra + 1) → α) → α

/-- Apply a local rule at every time coordinate. -/
def applyCode {α : Type} (code : LocalCode α) (y : ℕ → α) : ℕ → α :=
  fun t =>
    match code with
    | ⟨_, rule⟩ => rule (fun i => y (t + i.val))

/-- The identity one-step code. -/
def identityCode {α : Type} : LocalCode α :=
  ⟨0, fun block => block 0⟩

/-- Compose two local rules; the window over-approximation is additive in the extra budgets. -/
def composeCodes {α : Type} (first second : LocalCode α) : LocalCode α :=
  match first, second with
  | ⟨r, f⟩, ⟨s, g⟩ =>
      ⟨r + s, fun block =>
        g (fun j =>
          f (fun i =>
            block ⟨j.val + i.val, by
              have hj : j.val < s + 1 := j.isLt
              have hi : i.val < r + 1 := i.isLt
              omega⟩))⟩

/-- Running the composed code matches sequential application. -/
theorem apply_composeCodes {α : Type} (first second : LocalCode α) (y : ℕ → α) :
    applyCode (composeCodes first second) y = applyCode second (applyCode first y) := by
  cases first with
  | mk r f =>
      cases second with
      | mk s g =>
          funext t
          simp [applyCode, composeCodes, Nat.add_assoc]

/-- Sum of all extra window budgets. -/
def totalExtra {α : Type} : List (LocalCode α) → Nat
  | [] => 0
  | code :: codes => code.1 + totalExtra codes

/-- Sequential application of a list of local rules. -/
def runAll {α : Type} : List (LocalCode α) → (ℕ → α) → ℕ → α
  | [], y => y
  | code :: codes, y => runAll codes (applyCode code y)

/-- Collapse a finite list of local rules into a single local rule. -/
def collapseCodes {α : Type} : List (LocalCode α) → LocalCode α
  | [] => identityCode
  | code :: codes => composeCodes code (collapseCodes codes)

@[simp] theorem collapseCodes_extra_eq_totalExtra {α : Type} (codes : List (LocalCode α)) :
    (collapseCodes codes).1 = totalExtra codes := by
  induction codes with
  | nil =>
      rfl
  | cons code codes ih =>
      cases code with
      | mk extra rule =>
          simpa [collapseCodes, totalExtra, composeCodes] using congrArg (extra + ·) ih

/-- The collapsed code reproduces the whole finite refinement chain. -/
theorem apply_collapseCodes {α : Type} (codes : List (LocalCode α)) (y : ℕ → α) :
    applyCode (collapseCodes codes) y = runAll codes y := by
  induction codes generalizing y with
  | nil =>
      funext t
      rfl
  | cons code codes ih =>
      simpa [collapseCodes, runAll, apply_composeCodes] using ih (applyCode code y)

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for `thm:finite-depth-collapse`.
    A finite chain of one-sided sliding-block codes collapses to one code whose extra prefix budget
    is the sum of the intermediate extra budgets. -/
theorem paper_scan_projection_address_finite_depth_collapse_seeds
    {α : Type} (codes : List (LocalCode α)) :
    ∃ core : LocalCode α,
      core.1 = totalExtra codes ∧
      ∀ y, applyCode core y = runAll codes y := by
  refine ⟨collapseCodes codes, collapseCodes_extra_eq_totalExtra codes, ?_⟩
  intro y
  exact apply_collapseCodes codes y

/-- Packaged form of `thm:finite-depth-collapse`. -/
theorem paper_scan_projection_address_finite_depth_collapse_package
    {α : Type} (codes : List (LocalCode α)) :
    ∃ core : LocalCode α,
      core.1 = totalExtra codes ∧
      ∀ y, applyCode core y = runAll codes y :=
  paper_scan_projection_address_finite_depth_collapse_seeds codes

end Omega.RecursiveAddressing.FiniteDepthCollapse
