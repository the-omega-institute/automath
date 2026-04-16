import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion.FoldbinGroupoidTracialSimplex

open scoped BigOperators

/-- The normalized trace state of a single Wedderburn block, modeled as the corresponding
coordinate vertex of the standard simplex. -/
def normalizedBlockTrace
    {ι : Type} [DecidableEq ι] (w : ι) : ι → ℝ :=
  fun u => if u = w then 1 else 0

/-- Tracial states on a finite direct sum of matrix blocks, modeled by their simplex of block
weights. -/
def tracialSimplex
    {ι : Type} [Fintype ι] [DecidableEq ι] : Set (ι → ℝ) :=
  {τ | (∀ w, 0 ≤ τ w) ∧ Finset.univ.sum τ = 1}

/-- Escort weights coming from the block dimensions `d_w`. -/
noncomputable def escortWeight
    {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℕ) : ι → ℝ :=
  fun w => (d w : ℝ) ^ 2 / ∑ u, (d u : ℝ) ^ 2

set_option maxHeartbeats 400000 in
/-- Every point of the tracial simplex has the unique coordinate decomposition against the block
vertices. This is the simplex-side version of the blockwise trace decomposition. -/
theorem tracialSimplex_coordinate_decomposition
    {ι : Type} [Fintype ι] [DecidableEq ι] {τ : ι → ℝ}
    (hτ : τ ∈ tracialSimplex (ι := ι)) :
    ∃! α : ι → ℝ,
      (∀ w, 0 ≤ α w) ∧
        Finset.univ.sum α = 1 ∧
        τ = fun u => ∑ w, α w * normalizedBlockTrace w u := by
  rcases hτ with ⟨hτnonneg, hτsum⟩
  refine ⟨τ, ?_, ?_⟩
  · refine ⟨hτnonneg, hτsum, ?_⟩
    funext u
    simp [normalizedBlockTrace]
  · intro β hβ
    rcases hβ with ⟨_hβnonneg, _hβsum, hrepr⟩
    ext u
    have hEval := congrArg (fun f : ι → ℝ => f u) hrepr
    simpa [normalizedBlockTrace] using hEval.symm

set_option maxHeartbeats 400000 in
/-- The regular trace weights form a point of the tracial simplex. -/
theorem escortWeight_mem_tracialSimplex
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ι → ℕ) (hd : ∀ w, 0 < d w) :
    escortWeight d ∈ tracialSimplex (ι := ι) := by
  let denom : ℝ := ∑ u, (d u : ℝ) ^ 2
  have hdenom_pos : 0 < denom := by
    obtain ⟨w₀⟩ := ‹Nonempty ι›
    have hw₀ : 0 < (d w₀ : ℝ) := by
      exact_mod_cast hd w₀
    have hterm_pos : 0 < (d w₀ : ℝ) ^ 2 := by positivity
    have hsingle : (d w₀ : ℝ) ^ 2 ≤ denom := by
      dsimp [denom]
      exact
        Finset.single_le_sum (f := fun u => (d u : ℝ) ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ w₀)
    exact lt_of_lt_of_le hterm_pos hsingle
  refine ⟨?_, ?_⟩
  · intro w
    dsimp [escortWeight, denom]
    exact div_nonneg (by positivity) hdenom_pos.le
  · dsimp [escortWeight, denom]
    have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
    calc
      Finset.univ.sum (escortWeight d) = denom / denom := by
        simp [escortWeight, denom, Finset.sum_div]
      _ = 1 := by simp [hdenom_ne]

set_option maxHeartbeats 400000 in
/-- Paper-facing package: finite direct sums of matrix blocks have simplex-valued tracial states,
and the regular trace is the escort-weight point of that simplex. -/
theorem paper_conclusion_foldbin_groupoid_tracial_simplex_package
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ι → ℕ) (hd : ∀ w, 0 < d w) :
    let simplex := tracialSimplex (ι := ι)
    (∀ τ, τ ∈ simplex →
      ∃! α : ι → ℝ,
        (∀ w, 0 ≤ α w) ∧
          Finset.univ.sum α = 1 ∧
          τ = fun u => ∑ w, α w * normalizedBlockTrace w u) ∧
      escortWeight d ∈ simplex := by
  dsimp
  exact
    ⟨fun τ hτ => tracialSimplex_coordinate_decomposition hτ,
      escortWeight_mem_tracialSimplex d hd⟩

/-- Paper label wrapper for the Foldbin groupoid tracial-simplex theorem. -/
def paper_conclusion_foldbin_groupoid_tracial_simplex : Prop := by
  exact
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (d : ι → ℕ) (_hd : ∀ w, 0 < d w),
      let simplex := tracialSimplex (ι := ι)
      (∀ τ, τ ∈ simplex →
          ∃! α : ι → ℝ,
            (∀ w, 0 ≤ α w) ∧
              Finset.univ.sum α = 1 ∧
              τ = fun u => ∑ w, α w * normalizedBlockTrace w u) ∧
        escortWeight d ∈ simplex

end Omega.Conclusion.FoldbinGroupoidTracialSimplex
