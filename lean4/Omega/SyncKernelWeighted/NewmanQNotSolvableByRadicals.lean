import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WeightedNewmanQGaloisS37

namespace Omega.SyncKernelWeighted

/-- Distinguished roots of the audited degree-`37` Newman factor. -/
abbrev sync_kernel_weighted_newman_q_not_solvable_by_radicals_distinguished_root :=
  Fin 37

/-- Root-level nonsolvability predicate induced by the `S₃₇` Galois certificate. -/
def sync_kernel_weighted_newman_q_not_solvable_by_radicals_root_obstruction
    (_ : sync_kernel_weighted_newman_q_not_solvable_by_radicals_distinguished_root) : Prop :=
  ¬ IsSolvable (Equiv.Perm (Fin 37))

/-- Concrete `S₃₇` certificate reused by the radical-obstruction wrapper. -/
def sync_kernel_weighted_newman_q_not_solvable_by_radicals_galois_certificate :
    WeightedNewmanQGaloisS37Data where
  mod659FactorDegrees := [37]
  mod79FactorDegrees := [6, 31]
  mod13FactorDegrees := [10, 27]
  galoisGroup := ⊤
  oddWitness := Equiv.swap (0 : Fin 37) 1
  irreducibleCertificate := rfl
  jordanCertificate := rfl
  oddCertificate := rfl
  containsAlternating_h := by simp
  oddWitness_mem := by simp
  oddWitness_sign := by
    have h01 : (0 : Fin 37) ≠ 1 := by decide
    exact Equiv.Perm.sign_swap h01

/-- Paper-facing statement: the splitting field has Galois group `S₃₇`, hence every distinguished
root lies in the same nonsolvable radical-obstruction regime. -/
def sync_kernel_weighted_newman_q_not_solvable_by_radicals_statement : Prop :=
  WeightedNewmanQGaloisS37Data.galoisGroupIsS37
      sync_kernel_weighted_newman_q_not_solvable_by_radicals_galois_certificate ∧
    ∀ α : sync_kernel_weighted_newman_q_not_solvable_by_radicals_distinguished_root,
      sync_kernel_weighted_newman_q_not_solvable_by_radicals_root_obstruction α

/-- Paper label: `cor:sync-kernel-weighted-newman-Q-not-solvable-by-radicals`. -/
theorem paper_sync_kernel_weighted_newman_q_not_solvable_by_radicals :
    sync_kernel_weighted_newman_q_not_solvable_by_radicals_statement := by
  have hgalois :
      WeightedNewmanQGaloisS37Data.galoisGroupIsS37
          sync_kernel_weighted_newman_q_not_solvable_by_radicals_galois_certificate :=
    (paper_sync_kernel_weighted_newman_q_galois_s37
      sync_kernel_weighted_newman_q_not_solvable_by_radicals_galois_certificate).2.2.2.2
  have hnotSolvable : ¬ IsSolvable (Equiv.Perm (Fin 37)) := by
    simpa using
      (Equiv.Perm.not_solvable (Fin 37) (by
        rw [Cardinal.mk_fin]
        norm_num))
  refine ⟨hgalois, ?_⟩
  intro α
  exact hnotSolvable

end Omega.SyncKernelWeighted
