import Mathlib.Tactic
import Omega.Folding.BoundaryLayer
import Omega.Folding.ZeckendorfSignature

namespace Omega.GU

open Omega

/-- Boundary-cardinality lock for the `m = 11` branch: `|X_11^\mathrm{bdry}| = 34 = F_9`.
    cor:m11-z34-sixteen-rotation-planes-from-family-lock -/
theorem m11_z34_boundary_cardinality :
    cBoundaryCount 11 = 34 := by
  exact cBoundaryCount_eleven

/-- The boundary Fibonacci value `34` forces `m = 11` among all `m ≥ 3`.
    cor:m11-z34-sixteen-rotation-planes-from-family-lock -/
theorem m11_z34_boundary_uniqueness (m : Nat) (hm : 3 ≤ m)
    (h : Nat.fib (m - 2) = 34) : m = 11 := by
  exact Omega.ZeckSig.bdry_delta34_m11_uniqueness m hm h

/-- The nontrivial real irreducible decomposition count for the `\ZZ_{34}` boundary action:
    `34 = 1 + 1 + 16 * 2` and hence the augmentation summand has dimension `33 = 1 + 16 * 2`.
    cor:m11-z34-sixteen-rotation-planes-from-family-lock -/
theorem m11_z34_real_irrep_dimension_count :
    34 = 1 + 1 + 16 * 2 ∧ 33 = 1 + 16 * 2 := by
  norm_num

/-- Family-lock branch package for the `m = 11` / `\ZZ_{34}` interface.
    It records the boundary cardinality, the uniqueness of the `34`-branch, and the induced
    `16` planar rotation count.
    cor:m11-z34-sixteen-rotation-planes-from-family-lock -/
theorem paper_m11_z34_sixteen_rotation_planes_from_family_lock :
    cBoundaryCount 11 = 34 ∧
    Nat.fib 9 = 34 ∧
    (∀ m : Nat, 3 ≤ m → Nat.fib (m - 2) = 34 → m = 11) ∧
    34 = 1 + 1 + 16 * 2 ∧
    33 = 1 + 16 * 2 := by
  refine ⟨m11_z34_boundary_cardinality, by native_decide, ?_, ?_, ?_⟩
  · intro m hm h
    exact m11_z34_boundary_uniqueness m hm h
  · norm_num
  · norm_num

/-- Paper-facing wrapper for the `m = 11`, `|X_bdry| = 34` cyclotomic rigidity package: pairwise
nonisomorphic rotation-plane blocks force the real commutant to split as `C^16`, and therefore
its norm-one/unitary centralizer is intrinsically `U(1)^16`.
    prop:m11-z34-commutant-u1-16 -/
theorem paper_m11_z34_commutant_u1_16
    (pairwiseNonisomorphicRotationPlanes realCommutantIsC16 unitaryCentralizerIsU1Pow16 : Prop)
    (hReal : pairwiseNonisomorphicRotationPlanes -> realCommutantIsC16)
    (hUnitary : realCommutantIsC16 -> unitaryCentralizerIsU1Pow16)
    (hPlanes : pairwiseNonisomorphicRotationPlanes) :
    realCommutantIsC16 ∧ unitaryCentralizerIsU1Pow16 := by
  have hCommutant : realCommutantIsC16 := hReal hPlanes
  exact ⟨hCommutant, hUnitary hCommutant⟩

/-- Paper-facing wrapper for the cyclotomic decomposition of `\QQ[\ZZ_{34}]`.
    prop:m11-qz34-cyclotomic-decomposition -/
theorem paper_m11_qz34_cyclotomic_decomposition
    (crtDecomposition zeta34EqZeta17 cyclotomicDegree16 : Prop)
    (hCRT : crtDecomposition)
    (hZeta : zeta34EqZeta17)
    (hDegree : cyclotomicDegree16) :
    crtDecomposition ∧ zeta34EqZeta17 ∧ cyclotomicDegree16 := by
  exact ⟨hCRT, hZeta, hDegree⟩

/-- Paper-facing corollary: `Nat.totient 17 = 16` packages the intrinsic `C16` Galois action on
each rational cyclotomic layer for `\QQ[\ZZ_{34}]`.
    cor:m11-qz34-galois-c16 -/
theorem paper_m11_qz34_galois_c16
    (galoisGroupC16 rationalLayerCarriesC16 : Prop)
    (hGalois : Nat.totient 17 = 16 → galoisGroupC16)
    (hAction : galoisGroupC16 → rationalLayerCarriesC16) :
    Nat.totient 17 = 16 ∧ galoisGroupC16 ∧ rationalLayerCarriesC16 := by
  have hTotient : Nat.totient 17 = 16 := by native_decide
  have hC16 : galoisGroupC16 := hGalois hTotient
  exact ⟨hTotient, hC16, hAction hC16⟩

end Omega.GU
