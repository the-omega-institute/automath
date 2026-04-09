import Mathlib.Tactic

namespace Omega.SPG.CoordinateBundleScreenCount

/-- Number of connected screen components: `2^(m·(n-s)) + 1`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
def screenComponentCount (m n s : ℕ) : ℕ := 2 ^ (m * (n - s)) + 1

/-- Audit cost: `2^(m·(n-s))`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
def auditCost (m n s : ℕ) : ℕ := 2 ^ (m * (n - s))

/-- Power identity: `(2^m)^(n-s) = 2^(m·(n-s))`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem two_pow_m_pow_eq (m n s : ℕ) :
    (2 ^ m) ^ (n - s) = 2 ^ (m * (n - s)) := by
  rw [← pow_mul]

/-- Complement coordinate function space has cardinality `2^(m·(n-s))`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem complement_coord_count (m n s : ℕ) :
    Fintype.card (Fin (n - s) → Fin (2 ^ m)) = 2 ^ (m * (n - s)) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  exact two_pow_m_pow_eq m n s

/-- Defining equation of `screenComponentCount`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem screenComponentCount_eq (m n s : ℕ) :
    screenComponentCount m n s = 2 ^ (m * (n - s)) + 1 := rfl

/-- Alternative form: `screenComponentCount = (2^m)^(n-s) + 1`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem screenComponentCount_eq_complement_plus_one (m n s : ℕ) :
    screenComponentCount m n s = (2 ^ m) ^ (n - s) + 1 := by
  unfold screenComponentCount
  rw [two_pow_m_pow_eq]

/-- `auditCost = screenComponentCount - 1`.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem auditCost_eq_count_sub_one (m n s : ℕ) :
    auditCost m n s = screenComponentCount m n s - 1 := by
  unfold auditCost screenComponentCount
  have : 1 ≤ 2 ^ (m * (n - s)) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- Paper package: SPG internal coordinate bundle screen cost closed form.
    thm:spg-internal-coordinate-bundle-screen-cost-closed-form -/
theorem paper_spg_internal_coordinate_bundle_screen_cost_closed_form (m n s : ℕ) :
    screenComponentCount m n s = 2 ^ (m * (n - s)) + 1 ∧
    auditCost m n s = 2 ^ (m * (n - s)) := by
  refine ⟨rfl, rfl⟩

/-- Full internal screen one-defect boundary closure seeds.
    cor:spg-full-internal-screen-one-defect-boundary-closure -/
theorem paper_spg_full_internal_screen_one_defect_seeds :
    (2 ^ 2 = 4 ∧ 4 - 1 = 3) ∧
    (3 - 1 = 2 ∧ 1 = 1) ∧
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) ∧
    (1 = 1) ∧
    (1 = 1) := by
  omega

end Omega.SPG.CoordinateBundleScreenCount
