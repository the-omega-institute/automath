import Mathlib.Tactic

namespace Omega.Zeta

open Classical

/-- Finite-depth tower of prime slices, with a Boolean flag recording whether each layer is
genuinely branching. -/
structure XiPrimeSliceTower where
  depth : ℕ
  branching : Fin depth → Bool

/-- The subtype of genuinely branching layers. -/
def XiPrimeSliceBranchingLayer (T : XiPrimeSliceTower) :=
  { i : Fin T.depth // T.branching i = true }

instance (T : XiPrimeSliceTower) : DecidableEq (XiPrimeSliceBranchingLayer T) := by
  unfold XiPrimeSliceBranchingLayer
  infer_instance

instance (T : XiPrimeSliceTower) : Fintype (XiPrimeSliceBranchingLayer T) := by
  unfold XiPrimeSliceBranchingLayer
  infer_instance

/-- A prime-slice history records one Boolean choice for each genuinely branching layer. -/
abbrev XiPrimeSliceHistory (T : XiPrimeSliceTower) :=
  XiPrimeSliceBranchingLayer T → Bool

/-- Project a history to the coordinates retained by a chosen family of prime slices. -/
def xiPrimeSliceProject (T : XiPrimeSliceTower) (S : Finset (XiPrimeSliceBranchingLayer T)) :
    XiPrimeSliceHistory T → (S → Bool)
  | h, i => h i.1

/-- The all-trivial history. -/
def xiPrimeSliceZeroHistory (T : XiPrimeSliceTower) : XiPrimeSliceHistory T :=
  fun _ => false

/-- The history that is nontrivial only at the designated genuinely branching layer. -/
def xiPrimeSliceSingleLayerHistory (T : XiPrimeSliceTower) (j : XiPrimeSliceBranchingLayer T) :
    XiPrimeSliceHistory T :=
  fun i => if i = j then true else false

/-- Exact minimality means that keeping every genuinely branching layer is injective, while
dropping any one of them forces a collision. -/
def XiPrimeSliceExactMinimality (T : XiPrimeSliceTower) : Prop :=
  Function.Injective (xiPrimeSliceProject T Finset.univ) ∧
    ∀ S : Finset (XiPrimeSliceBranchingLayer T), S ⊂ Finset.univ →
      ¬ Function.Injective (xiPrimeSliceProject T S)

/-- Paper label: `thm:xi-prime-slice-nontrivial-layer-exact-minimality`. -/
theorem paper_xi_prime_slice_nontrivial_layer_exact_minimality (T : XiPrimeSliceTower) :
    XiPrimeSliceExactMinimality T := by
  refine ⟨?_, ?_⟩
  · intro h₁ h₂ hEq
    funext i
    have hcoord := congrFun hEq ⟨i, by simp⟩
    simpa [xiPrimeSliceProject] using hcoord
  · intro S hS hInj
    have hne : S ≠ Finset.univ := ne_of_lt hS
    have hmissing : ∃ j : XiPrimeSliceBranchingLayer T, j ∉ S := by
      by_contra hAll
      apply hne
      ext j
      simp [not_exists] at hAll
      simp [hAll j]
    rcases hmissing with ⟨j, hjS⟩
    let h₀ := xiPrimeSliceZeroHistory T
    let h₁ := xiPrimeSliceSingleLayerHistory T j
    have hproj : xiPrimeSliceProject T S h₀ = xiPrimeSliceProject T S h₁ := by
      funext i
      have hij : (i : XiPrimeSliceBranchingLayer T) ≠ j := by
        intro hij
        apply hjS
        simpa [hij] using i.2
      simp [xiPrimeSliceProject, h₀, h₁, xiPrimeSliceZeroHistory, xiPrimeSliceSingleLayerHistory,
        hij]
    have hhist : h₀ = h₁ := hInj hproj
    have hjcoord := congrFun hhist j
    have : False := by
      simpa [h₀, h₁, xiPrimeSliceZeroHistory, xiPrimeSliceSingleLayerHistory] using hjcoord
    exact this

end Omega.Zeta
