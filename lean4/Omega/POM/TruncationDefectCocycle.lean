import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

namespace Omega.POM

universe u v

/-- Concrete prefix-system data for the naive truncation defect cocycle. The value groups are
written additively; the hypothesis `x + x = 0` records that addition is the vector-space xor. -/
structure pom_truncation_defect_cocycle_data where
  pom_truncation_defect_cocycle_state : ℕ → Type u
  pom_truncation_defect_cocycle_value : ℕ → Type v
  pom_truncation_defect_cocycle_value_group :
    ∀ n : ℕ, AddCommGroup (pom_truncation_defect_cocycle_value n)
  pom_truncation_defect_cocycle_xor_self :
    ∀ {n : ℕ} (x : pom_truncation_defect_cocycle_value n), x + x = 0
  pom_truncation_defect_cocycle_tau :
    ∀ {m n : ℕ}, m ≤ n →
      pom_truncation_defect_cocycle_state n → pom_truncation_defect_cocycle_state m
  pom_truncation_defect_cocycle_pi :
    ∀ {m n : ℕ}, m ≤ n →
      pom_truncation_defect_cocycle_value n → pom_truncation_defect_cocycle_value m
  pom_truncation_defect_cocycle_fold :
    ∀ n : ℕ, pom_truncation_defect_cocycle_state n → pom_truncation_defect_cocycle_value n
  pom_truncation_defect_cocycle_tau_refl :
    ∀ {n : ℕ} (x : pom_truncation_defect_cocycle_state n),
      pom_truncation_defect_cocycle_tau (le_refl n) x = x
  pom_truncation_defect_cocycle_pi_refl :
    ∀ {n : ℕ} (x : pom_truncation_defect_cocycle_value n),
      pom_truncation_defect_cocycle_pi (le_refl n) x = x
  pom_truncation_defect_cocycle_tau_functorial :
    ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
      (x : pom_truncation_defect_cocycle_state n),
      pom_truncation_defect_cocycle_tau (le_trans hlm hmn) x =
        pom_truncation_defect_cocycle_tau hlm (pom_truncation_defect_cocycle_tau hmn x)
  pom_truncation_defect_cocycle_pi_add :
    ∀ {m n : ℕ} (hmn : m ≤ n)
      (x y : pom_truncation_defect_cocycle_value n),
      pom_truncation_defect_cocycle_pi hmn (x + y) =
        pom_truncation_defect_cocycle_pi hmn x + pom_truncation_defect_cocycle_pi hmn y
  pom_truncation_defect_cocycle_pi_functorial :
    ∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
      (x : pom_truncation_defect_cocycle_value n),
      pom_truncation_defect_cocycle_pi (le_trans hlm hmn) x =
        pom_truncation_defect_cocycle_pi hlm (pom_truncation_defect_cocycle_pi hmn x)

attribute [instance] pom_truncation_defect_cocycle_data.pom_truncation_defect_cocycle_value_group

/-- The truncation defect comparing folding after prefixing with prefixing after folding. -/
def pom_truncation_defect_cocycle_defect
    (D : pom_truncation_defect_cocycle_data) {m n : ℕ} (hmn : m ≤ n)
    (x : D.pom_truncation_defect_cocycle_state n) :
    D.pom_truncation_defect_cocycle_value m :=
  D.pom_truncation_defect_cocycle_fold m (D.pom_truncation_defect_cocycle_tau hmn x) +
    D.pom_truncation_defect_cocycle_pi hmn
      (D.pom_truncation_defect_cocycle_fold n x)

/-- Cocycle and identity laws for the concrete truncation defect. -/
def pom_truncation_defect_cocycle_statement
    (D : pom_truncation_defect_cocycle_data) : Prop :=
  (∀ {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
      (x : D.pom_truncation_defect_cocycle_state n),
      pom_truncation_defect_cocycle_defect D (le_trans hlm hmn) x =
        pom_truncation_defect_cocycle_defect D hlm
          (D.pom_truncation_defect_cocycle_tau hmn x) +
          D.pom_truncation_defect_cocycle_pi hlm
            (pom_truncation_defect_cocycle_defect D hmn x)) ∧
    ∀ {n : ℕ} (x : D.pom_truncation_defect_cocycle_state n),
      pom_truncation_defect_cocycle_defect D (le_refl n) x = 0

/-- Paper label: `lem:pom-truncation-defect-cocycle`. The naive truncation defect is a
characteristic-two cocycle, and the identity truncation has zero defect. -/
theorem paper_pom_truncation_defect_cocycle (D : pom_truncation_defect_cocycle_data) :
    pom_truncation_defect_cocycle_statement D := by
  constructor
  · intro l m n hlm hmn x
    unfold pom_truncation_defect_cocycle_defect
    rw [D.pom_truncation_defect_cocycle_tau_functorial hlm hmn x]
    rw [D.pom_truncation_defect_cocycle_pi_add hlm]
    rw [D.pom_truncation_defect_cocycle_pi_functorial hlm hmn]
    let a : D.pom_truncation_defect_cocycle_value l :=
      D.pom_truncation_defect_cocycle_fold l
        (D.pom_truncation_defect_cocycle_tau hlm
          (D.pom_truncation_defect_cocycle_tau hmn x))
    let b : D.pom_truncation_defect_cocycle_value l :=
      D.pom_truncation_defect_cocycle_pi hlm
        (D.pom_truncation_defect_cocycle_fold m
          (D.pom_truncation_defect_cocycle_tau hmn x))
    let c : D.pom_truncation_defect_cocycle_value l :=
      D.pom_truncation_defect_cocycle_pi hlm
        (D.pom_truncation_defect_cocycle_pi hmn
          (D.pom_truncation_defect_cocycle_fold n x))
    change a + c = (a + b) + (b + c)
    symm
    calc
      (a + b) + (b + c) = a + (b + b) + c := by abel
      _ = a + 0 + c := by rw [D.pom_truncation_defect_cocycle_xor_self b]
      _ = a + c := by simp
  · intro n x
    simp [pom_truncation_defect_cocycle_defect,
      D.pom_truncation_defect_cocycle_tau_refl,
      D.pom_truncation_defect_cocycle_pi_refl,
      D.pom_truncation_defect_cocycle_xor_self]

end Omega.POM
