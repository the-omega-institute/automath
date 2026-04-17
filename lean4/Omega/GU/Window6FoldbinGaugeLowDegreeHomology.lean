import Mathlib.Tactic
import Omega.Folding.Window6

namespace Omega.GU

/-- Concrete window-`6` low-degree homology package. The content is determined by the explicit
window-`6` fiber histogram, so the carrier itself is empty and the paper-facing statements are
computed definitions. -/
structure Window6FoldbinGaugeLowDegreeHomologyData where

namespace Window6FoldbinGaugeLowDegreeHomologyData

/-- `N₂`: the number of fibers of multiplicity at least `2`. -/
def n2 (_ : Window6FoldbinGaugeLowDegreeHomologyData) : ℕ :=
  Omega.cFiberHist 6 2 + Omega.cFiberHist 6 3 + Omega.cFiberHist 6 4 + Omega.cFiberHist 6 5

/-- `N₄`: the number of fibers of multiplicity at least `4`. -/
def n4 (_ : Window6FoldbinGaugeLowDegreeHomologyData) : ℕ :=
  Omega.cFiberHist 6 4 + Omega.cFiberHist 6 5

/-- The capacity curve `C(t) = Σ_w min(d(w), t)` specialized to the window-`6` histogram. -/
def capacityCurve (_ : Window6FoldbinGaugeLowDegreeHomologyData) (t : ℕ) : ℕ :=
  Omega.cFiberHist 6 1 * Nat.min 1 t +
    Omega.cFiberHist 6 2 * Nat.min 2 t +
    Omega.cFiberHist 6 3 * Nat.min 3 t +
    Omega.cFiberHist 6 4 * Nat.min 4 t +
    Omega.cFiberHist 6 5 * Nat.min 5 t

/-- `H₁` rank over `ℤ₂`. -/
def h1Rank (D : Window6FoldbinGaugeLowDegreeHomologyData) : ℕ :=
  D.n2

/-- `H₂` rank over `ℤ₂`. -/
def h2Rank (D : Window6FoldbinGaugeLowDegreeHomologyData) : ℕ :=
  D.n4 + Nat.choose D.n2 2

/-- `H²(-; ℤ₂)` rank. -/
def h2CohomologyRank (D : Window6FoldbinGaugeLowDegreeHomologyData) : ℕ :=
  D.n4 + Nat.choose (D.n2 + 1) 2

/-- The closed form `H₁ ≅ (ℤ₂)^{N₂}` specializes to rank `19` for window `6`. -/
def h1ClosedForm (D : Window6FoldbinGaugeLowDegreeHomologyData) : Prop :=
  D.h1Rank = 19

/-- The closed form `H₂ ≅ (ℤ₂)^{N₄ + (N₂ choose 2)}` specializes to rank `178`. -/
def h2ClosedForm (D : Window6FoldbinGaugeLowDegreeHomologyData) : Prop :=
  D.h2Rank = 178

/-- The closed form `H²(-; ℤ₂) ≅ (ℤ₂)^{N₄ + (N₂ + 1 choose 2)}` specializes to rank `197`. -/
def h2CohomologyClosedForm (D : Window6FoldbinGaugeLowDegreeHomologyData) : Prop :=
  D.h2CohomologyRank = 197

/-- The capacity-curve jumps recover `N₂` and `N₄`. -/
def capacityThresholdRecovery (D : Window6FoldbinGaugeLowDegreeHomologyData) : Prop :=
  D.n2 = D.capacityCurve 2 - D.capacityCurve 1 ∧
    D.n4 = D.capacityCurve 4 - D.capacityCurve 3

@[simp] theorem n2_eq (D : Window6FoldbinGaugeLowDegreeHomologyData) : D.n2 = 19 := by
  dsimp [n2]
  rw [Omega.cFiberHist_6_2, Omega.cFiberHist_6_3, Omega.cFiberHist_6_4, Omega.cFiberHist_6_5]

@[simp] theorem n4_eq (D : Window6FoldbinGaugeLowDegreeHomologyData) : D.n4 = 7 := by
  dsimp [n4]
  rw [Omega.cFiberHist_6_4, Omega.cFiberHist_6_5]

@[simp] theorem capacityCurve_one (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.capacityCurve 1 = 21 := by
  dsimp [capacityCurve]
  rw [Omega.cFiberHist_6_1, Omega.cFiberHist_6_2, Omega.cFiberHist_6_3, Omega.cFiberHist_6_4,
    Omega.cFiberHist_6_5]
  native_decide

@[simp] theorem capacityCurve_two (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.capacityCurve 2 = 40 := by
  dsimp [capacityCurve]
  rw [Omega.cFiberHist_6_1, Omega.cFiberHist_6_2, Omega.cFiberHist_6_3, Omega.cFiberHist_6_4,
    Omega.cFiberHist_6_5]
  native_decide

@[simp] theorem capacityCurve_three (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.capacityCurve 3 = 55 := by
  dsimp [capacityCurve]
  rw [Omega.cFiberHist_6_1, Omega.cFiberHist_6_2, Omega.cFiberHist_6_3, Omega.cFiberHist_6_4,
    Omega.cFiberHist_6_5]
  native_decide

@[simp] theorem capacityCurve_four (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.capacityCurve 4 = 62 := by
  dsimp [capacityCurve]
  rw [Omega.cFiberHist_6_1, Omega.cFiberHist_6_2, Omega.cFiberHist_6_3, Omega.cFiberHist_6_4,
    Omega.cFiberHist_6_5]
  native_decide

@[simp] theorem h1ClosedForm_true (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.h1ClosedForm := by
  simp [h1ClosedForm, h1Rank]

@[simp] theorem h2ClosedForm_true (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.h2ClosedForm := by
  dsimp [h2ClosedForm, h2Rank]
  rw [D.n2_eq, D.n4_eq]
  native_decide

@[simp] theorem h2CohomologyClosedForm_true (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.h2CohomologyClosedForm := by
  dsimp [h2CohomologyClosedForm, h2CohomologyRank]
  rw [D.n2_eq, D.n4_eq]
  native_decide

@[simp] theorem capacityThresholdRecovery_true (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.capacityThresholdRecovery := by
  dsimp [capacityThresholdRecovery]
  rw [D.n2_eq, D.n4_eq, D.capacityCurve_one, D.capacityCurve_two, D.capacityCurve_three,
    D.capacityCurve_four]
  native_decide

end Window6FoldbinGaugeLowDegreeHomologyData

/-- For the window-`6` bin-fold gauge group, the low-degree homology is determined by the threshold
counts `N₂` and `N₄`, and those threshold counts are read off from the capacity-curve jumps.
    thm:window6-foldbin-gauge-low-degree-homology -/
theorem paper_window6_foldbin_gauge_low_degree_homology
    (D : Window6FoldbinGaugeLowDegreeHomologyData) :
    D.h1ClosedForm ∧ D.h2ClosedForm ∧ D.h2CohomologyClosedForm ∧ D.capacityThresholdRecovery := by
  exact ⟨D.h1ClosedForm_true, D.h2ClosedForm_true, D.h2CohomologyClosedForm_true,
    D.capacityThresholdRecovery_true⟩

end Omega.GU
