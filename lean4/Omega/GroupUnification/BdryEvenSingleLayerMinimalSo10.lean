import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.GroupUnification

/-- The compact simple types used in the local dimension-45 classification step. -/
inductive CompactSimpleType where
  | su2
  | su3
  | so10
  | e6
  deriving DecidableEq

/-- The corresponding compact-simple dimensions. -/
def compactSimpleDimension : CompactSimpleType → ℕ
  | .su2 => 3
  | .su3 => 8
  | .so10 => 45
  | .e6 => 78

/-- The even single-layer boundary condition above the low-rank window. -/
def bdryEvenSingleLayerAdmissible (m : ℕ) : Prop :=
  8 < m ∧ 2 ∣ Nat.fib (m - 2)

/-- The resulting boundary dimension package. -/
def bdryEvenSingleLayerDimension (m : ℕ) : ℕ :=
  Nat.fib (m - 2) + Nat.fib 6 + Nat.fib 4

private theorem bdryEvenSingleLayer_min_index (m : ℕ)
    (hm : bdryEvenSingleLayerAdmissible m) : 11 ≤ m := by
  rcases hm with ⟨hmgt, hEven⟩
  have h3 : 3 ∣ (m - 2) := (Omega.fib_even_iff_three_dvd (m - 2)).mp hEven
  rcases h3 with ⟨k, hk⟩
  omega

private theorem compactSimple_dim45_unique (G : CompactSimpleType)
    (hG : compactSimpleDimension G = 45) : G = CompactSimpleType.so10 := by
  cases G
  · simp [compactSimpleDimension] at hG
  · simp [compactSimpleDimension] at hG
  · rfl
  · simp [compactSimpleDimension] at hG

/-- Even Fibonacci single-layer boundary data above rank eight first occurs at `m = 11`, giving
the boundary dimension `45`; among the local compact-simple candidates, dimension `45` is exactly
`so(10)`.
    thm:bdry-even-single-layer-minimal-so10 -/
theorem paper_bdry_even_single_layer_minimal_so10 :
    bdryEvenSingleLayerAdmissible 11 ∧
    (∀ m : ℕ, bdryEvenSingleLayerAdmissible m → 11 ≤ m) ∧
    bdryEvenSingleLayerDimension 11 = 45 ∧
    (∀ G : CompactSimpleType,
      compactSimpleDimension G = bdryEvenSingleLayerDimension 11 → G = CompactSimpleType.so10) :=
    by
  refine ⟨?_, bdryEvenSingleLayer_min_index, ?_, ?_⟩
  · refine ⟨by omega, ?_⟩
    have h3 : 3 ∣ (11 - 2) := ⟨3, by decide⟩
    exact (Omega.fib_even_iff_three_dvd (11 - 2)).mpr h3
  · native_decide
  · intro G hG
    apply compactSimple_dim45_unique G
    simpa [bdryEvenSingleLayerDimension] using hG

end Omega.GroupUnification
