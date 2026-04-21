import Mathlib

namespace Omega.Folding

open scoped BigOperators

/-- The thermal kernel extracted from the cross-fiber edge counts. -/
def foldThermalKernel {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (d : α → ℕ) (E : α → α → ℕ) : α → α → ℚ :=
  fun x y => (E x y : ℚ) / ((m * d x : ℕ) : ℚ)

/-- The stationary law induced by the fiber multiplicities. -/
def foldThermalStationary {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (d : α → ℕ) : α → ℚ :=
  fun x => (d x : ℚ) / ((2 ^ m : ℕ) : ℚ)

/-- Row-stochasticity of the thermal kernel. -/
def foldThermalRowStochastic {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (d : α → ℕ) (E : α → α → ℕ) : Prop :=
  ∀ x, ∑ y, foldThermalKernel m d E x y = 1

/-- Detailed balance with respect to the fiber-size stationary law. -/
def foldThermalDetailedBalance {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (d : α → ℕ) (E : α → α → ℕ) : Prop :=
  ∀ x y,
    foldThermalStationary m d x * foldThermalKernel m d E x y =
      foldThermalStationary m d y * foldThermalKernel m d E y x

/-- The edge-count kernel is stochastic and reversible, and its flux is the normalized edge count.
-/
def foldThermalIsKernel {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (d : α → ℕ) (E : α → α → ℕ) : Prop :=
  foldThermalRowStochastic m d E ∧
    foldThermalDetailedBalance m d E ∧
    (∀ x y,
      foldThermalStationary m d x * foldThermalKernel m d E x y =
        (E x y : ℚ) / ((m * 2 ^ m : ℕ) : ℚ))

private lemma foldThermal_kernel_row_stochastic {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (hm : 0 < m) (d : α → ℕ) (hd : ∀ x, 0 < d x) (E : α → α → ℕ)
    (hrowsum : ∀ x, ∑ y, E x y = m * d x) :
    foldThermalRowStochastic m d E := by
  intro x
  have hmd_ne : (((m * d x : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero hm.ne' (Nat.ne_of_gt (hd x))
  have hrow : ((∑ y, E x y : ℕ) : ℚ) = ((m * d x : ℕ) : ℚ) := by
    exact_mod_cast hrowsum x
  calc
    ∑ y, foldThermalKernel m d E x y
        = (∑ y, (E x y : ℚ)) / (((m * d x : ℕ) : ℚ)) := by
            simp [foldThermalKernel, Finset.sum_div]
    _ = (((m * d x : ℕ) : ℚ)) / (((m * d x : ℕ) : ℚ)) := by simpa using congrArg (fun z : ℚ => z / (((m * d x : ℕ) : ℚ))) hrow
    _ = 1 := by field_simp [hmd_ne]

private lemma foldThermal_flux_formula {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (hm : 0 < m) (d : α → ℕ) (hd : ∀ x, 0 < d x) (E : α → α → ℕ) :
    ∀ x y,
      foldThermalStationary m d x * foldThermalKernel m d E x y =
        (E x y : ℚ) / ((m * 2 ^ m : ℕ) : ℚ) := by
  intro x y
  have hm_ne : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdx_ne : ((d x : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hd x))
  have hpow_ne : (((2 ^ m : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero m (show (2 : ℕ) ≠ 0 by decide)
  unfold foldThermalStationary foldThermalKernel
  field_simp [hm_ne, hdx_ne, hpow_ne]
  push_cast
  ring

/-- Paper label: `prop:fold-thermal-kernel-from-edge-count`. Symmetry of the cross-fiber edge
count matrix and the fiberwise row-sum identity force the normalized edge-count kernel to be
stochastic and reversible with the stationary law proportional to fiber size. -/
theorem paper_fold_thermal_kernel_from_edge_count {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (hm : 0 < m) (d : α → ℕ) (hd : ∀ x, 0 < d x) (E : α → α → ℕ)
    (hsymm : ∀ x y, E x y = E y x) (_hdiag : ∀ x, E x x = 0) (hrowsum : ∀ x, ∑ y, E x y = m * d x) :
    foldThermalIsKernel m d E := by
  refine ⟨foldThermal_kernel_row_stochastic m hm d hd E hrowsum, ?_, ?_⟩
  · intro x y
    rw [foldThermal_flux_formula m hm d hd E x y, foldThermal_flux_formula m hm d hd E y x,
      hsymm x y]
  · exact foldThermal_flux_formula m hm d hd E

end Omega.Folding
