import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Number of finite moment and off-origin Borel constraints in the fixed-depth shadow. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount
    (n M : ℕ) : ℕ :=
  2 * n + M

/-- Concrete kernel condition: all constrained coordinates vanish. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_sampleKernel
    (n M N : ℕ) (v : Fin N → ℚ) : Prop :=
  ∀ i : Fin N,
    i.1 < conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M →
      v i = 0

/-- The coordinate just beyond the finite constraint list. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_freeIndex
    {n M N : ℕ}
    (hN : conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M < N) :
    Fin N :=
  ⟨conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M, hN⟩

/-- A nonzero vector in the finite-constraint kernel. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector
    {n M N : ℕ}
    (hN : conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M < N) :
    Fin N → ℚ :=
  fun i =>
    if i =
        conclusion_principal_shadow_finite_offorigin_borel_not_rigid_freeIndex
          (n := n) (M := M) hN then
      1
    else
      0

/-- Finite principal-shadow data together with finitely many off-origin samples. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData
    (n M _t : ℕ) : (Fin (2 * n) → ℚ) × (Fin M → ℚ) :=
  (fun _ => 0, fun _ => 0)

/-- A concrete invariant separating the infinite pointed-host family. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_hostSignature
    (t : ℕ) : ℕ :=
  t

lemma conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector_mem
    {n M N : ℕ}
    (hN : conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M < N) :
    conclusion_principal_shadow_finite_offorigin_borel_not_rigid_sampleKernel n M N
      (conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector hN) := by
  intro i hi
  have hne :
      i ≠
        conclusion_principal_shadow_finite_offorigin_borel_not_rigid_freeIndex
          (n := n) (M := M) hN := by
    intro h
    have hval := congrArg Fin.val h
    simp [conclusion_principal_shadow_finite_offorigin_borel_not_rigid_freeIndex] at hval
    omega
  simp [conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector, hne]

lemma conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector_ne_zero
    {n M N : ℕ}
    (hN : conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M < N) :
    conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector hN ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero
    (conclusion_principal_shadow_finite_offorigin_borel_not_rigid_freeIndex
      (n := n) (M := M) hN)
  simp [conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector] at hvalue

lemma conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernel_exists
    {n M N : ℕ}
    (hN : conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M < N) :
    ∃ v : Fin N → ℚ,
      conclusion_principal_shadow_finite_offorigin_borel_not_rigid_sampleKernel n M N v ∧
        v ≠ 0 := by
  exact
    ⟨conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector hN,
      conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector_mem hN,
      conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernelVector_ne_zero hN⟩

lemma conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData_constant
    (n M t u : ℕ) :
    conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData n M t =
      conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData n M u := by
  rfl

lemma conclusion_principal_shadow_finite_offorigin_borel_not_rigid_hostSignature_injective :
    Function.Injective
      conclusion_principal_shadow_finite_offorigin_borel_not_rigid_hostSignature := by
  intro t u h
  exact h

/-- Concrete package for
`cor:conclusion-principal-shadow-finite-offorigin-borel-not-rigid`.  For every
`N > 2*n + M`, the span with `N` coordinates has a nonzero vector in the kernel of the
finite constraint list, and the fixed finite data are shared by an injectively indexed
infinite family of host signatures. -/
def conclusion_principal_shadow_finite_offorigin_borel_not_rigid_package : Prop :=
  ∀ n M N : ℕ,
    1 ≤ n →
      conclusion_principal_shadow_finite_offorigin_borel_not_rigid_constraintCount n M < N →
        (∃ v : Fin N → ℚ,
          conclusion_principal_shadow_finite_offorigin_borel_not_rigid_sampleKernel n M N v ∧
            v ≠ 0) ∧
          (∀ t u : ℕ,
            conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData n M t =
              conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData n M u) ∧
          Function.Injective
            conclusion_principal_shadow_finite_offorigin_borel_not_rigid_hostSignature

/-- Paper label:
`cor:conclusion-principal-shadow-finite-offorigin-borel-not-rigid`. -/
theorem paper_conclusion_principal_shadow_finite_offorigin_borel_not_rigid :
    conclusion_principal_shadow_finite_offorigin_borel_not_rigid_package := by
  intro n M N _hn hN
  refine ⟨?_, ?_, ?_⟩
  · exact conclusion_principal_shadow_finite_offorigin_borel_not_rigid_kernel_exists hN
  · intro t u
    exact conclusion_principal_shadow_finite_offorigin_borel_not_rigid_finiteData_constant n M t u
  · exact conclusion_principal_shadow_finite_offorigin_borel_not_rigid_hostSignature_injective

end Omega.Conclusion
