import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The natural endpoint of the min-kernel interval. -/
noncomputable def minKernelEndpoint : ℝ := Real.log 2

/-- The closed interval `[0, log 2]` used by the min-kernel formulas. -/
def MinKernelDomain (x : ℝ) : Prop := x ∈ Set.Icc (0 : ℝ) minKernelEndpoint

/-- Pointwise min-kernel projection. -/
def T_min (a x : ℝ) : ℝ := max 0 (x - a)

/-- Pointwise min-kernel inversion candidate. -/
noncomputable def E_min (a y : ℝ) : ℝ := min minKernelEndpoint (y + a)

/-- Symmetric min-kernel gauge. -/
def G_min (a α : ℝ) : ℝ := max (T_min a α) (T_min α a)

lemma T_min_E_min_galois {a x y : ℝ} (_ha : MinKernelDomain a) (hx : MinKernelDomain x)
    (hy : MinKernelDomain y) :
    T_min a x ≤ y ↔ x ≤ E_min a y := by
  constructor
  · intro h
    have hsub : x - a ≤ y := le_trans (le_max_right 0 (x - a)) h
    refine le_min hx.2 ?_
    linarith
  · intro h
    have hsub : x - a ≤ y := by
      have h' : x ≤ y + a := le_trans h (min_le_right _ _)
      linarith
    exact (max_le_iff.mpr ⟨hy.1, hsub⟩)

lemma exact_recovery {a g : ℝ} (_ha : MinKernelDomain a) (hg : MinKernelDomain g)
    (hga : g + a ≤ minKernelEndpoint) :
    T_min a (E_min a g) = g := by
  rw [E_min, min_eq_right hga, T_min]
  have hsub : g + a - a = g := by ring
  rw [hsub, max_eq_right hg.1]

lemma G_min_eq_abs {a α : ℝ} :
    G_min a α = |a - α| := by
  by_cases h : a ≤ α
  · have h1 : T_min a α = α - a := by
      rw [T_min, max_eq_right]
      linarith
    have h2 : T_min α a = 0 := by
      rw [T_min, max_eq_left]
      linarith
    rw [G_min, h1, h2, max_eq_left]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · linarith
  · have h' : α ≤ a := le_of_not_ge h
    have h1 : T_min a α = 0 := by
      rw [T_min, max_eq_left]
      linarith
    have h2 : T_min α a = a - α := by
      rw [T_min, max_eq_right]
      linarith
    rw [G_min, h1, h2, max_eq_right]
    · rw [abs_of_nonneg]
      linarith
    · linarith

end Omega.POM

/-- Paper-facing min-kernel projection and inversion package on `[0, log 2]`: the pointwise
Galois adjunction, the maximal-preimage clause, exact recovery when the truncated inverse stays
inside the interval, and the symmetric gauge simplification.
    thm:pom-min-kernel-projection-and-inversion -/
theorem paper_pom_min_kernel_projection_and_inversion :
    (∀ {a x y : ℝ}, Omega.POM.MinKernelDomain a → Omega.POM.MinKernelDomain x →
      Omega.POM.MinKernelDomain y → (Omega.POM.T_min a x ≤ y ↔ x ≤ Omega.POM.E_min a y)) ∧
    (∀ {a f g : ℝ}, Omega.POM.MinKernelDomain a → Omega.POM.MinKernelDomain f →
      Omega.POM.MinKernelDomain g → Omega.POM.T_min a f ≤ g → f ≤ Omega.POM.E_min a g) ∧
    (∀ {a g : ℝ}, Omega.POM.MinKernelDomain a → Omega.POM.MinKernelDomain g →
      g + a ≤ Omega.POM.minKernelEndpoint → Omega.POM.T_min a (Omega.POM.E_min a g) = g) ∧
    (∀ {a α : ℝ}, Omega.POM.MinKernelDomain a → Omega.POM.MinKernelDomain α →
      Omega.POM.G_min a α = |a - α|) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a x y ha hx hy
    exact Omega.POM.T_min_E_min_galois ha hx hy
  · intro a f g ha hf hg hfg
    exact (Omega.POM.T_min_E_min_galois ha hf hg).1 hfg
  · intro a g ha hg hga
    exact Omega.POM.exact_recovery ha hg hga
  · intro a α ha hα
    let _ := ha
    let _ := hα
    exact Omega.POM.G_min_eq_abs
