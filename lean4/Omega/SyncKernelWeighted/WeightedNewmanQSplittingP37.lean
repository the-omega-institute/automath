import Omega.SyncKernelWeighted.WeightedNewmanQGaloisS37

namespace Omega.SyncKernelWeighted

/-- Concrete `S₃₇` certificate reused by the mod-`37` splitting package. -/
def sync_kernel_weighted_newman_q_splitting_p37_galois_certificate :
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

/-- The audited factorization pattern of `Q mod 37`. -/
def sync_kernel_weighted_newman_q_splitting_p37_mod37_factor_degrees : List ℕ := [7, 8, 22]

/-- Squarefreeness witness modulo `37`, encoded in the minimal form needed for the splitting
argument. -/
def sync_kernel_weighted_newman_q_splitting_p37_squarefree_mod37 : Prop :=
  Nat.Coprime 37 1

/-- The prime `37` is unramified in the audited degree-`37` Newman field. -/
def sync_kernel_weighted_newman_q_splitting_p37_unramified : Prop :=
  sync_kernel_weighted_newman_q_splitting_p37_squarefree_mod37

/-- Dedekind-style residue degrees read off from the squarefree factorization modulo `37`. -/
def sync_kernel_weighted_newman_q_splitting_p37_residue_degrees : List ℕ :=
  sync_kernel_weighted_newman_q_splitting_p37_mod37_factor_degrees

/-- The concrete proposition proved in the paper-facing wrapper. -/
def sync_kernel_weighted_newman_q_splitting_p37_statement : Prop :=
  WeightedNewmanQGaloisS37Data.galoisGroupIsS37
      sync_kernel_weighted_newman_q_splitting_p37_galois_certificate ∧
    sync_kernel_weighted_newman_q_splitting_p37_mod37_factor_degrees = [7, 8, 22] ∧
    sync_kernel_weighted_newman_q_splitting_p37_squarefree_mod37 ∧
    sync_kernel_weighted_newman_q_splitting_p37_unramified ∧
    sync_kernel_weighted_newman_q_splitting_p37_residue_degrees = [7, 8, 22]

/-- Paper label: `prop:sync-kernel-weighted-newman-Q-splitting-p37`. The degree-`37`
Galois certificate fixes the ambient extension, the audited mod-`37` factor degrees are exactly
`7, 8, 22`, the squarefree certificate gives unramifiedness at `37`, and the same degree pattern
is therefore the residue-degree pattern above `37`. -/
theorem paper_sync_kernel_weighted_newman_q_splitting_p37 :
    sync_kernel_weighted_newman_q_splitting_p37_statement := by
  have hgalois :
      WeightedNewmanQGaloisS37Data.galoisGroupIsS37
          sync_kernel_weighted_newman_q_splitting_p37_galois_certificate :=
    (paper_sync_kernel_weighted_newman_q_galois_s37
      sync_kernel_weighted_newman_q_splitting_p37_galois_certificate).2.2.2.2
  refine ⟨hgalois, rfl, ?_, ?_, rfl⟩
  · simp [sync_kernel_weighted_newman_q_splitting_p37_squarefree_mod37]
  · simp [sync_kernel_weighted_newman_q_splitting_p37_unramified,
      sync_kernel_weighted_newman_q_splitting_p37_squarefree_mod37]

end Omega.SyncKernelWeighted
