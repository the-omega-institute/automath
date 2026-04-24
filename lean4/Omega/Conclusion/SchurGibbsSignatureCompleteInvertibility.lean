import Mathlib.Tactic
import Omega.POM.SchurPlancherelEnergyIdentity

namespace Omega.Conclusion

noncomputable section

open Omega.POM
open Omega.POM.SchurPartitionIndex
open scoped BigOperators

/-- Forward Schur-character transform on the concrete `S₂` Gibbs signature space. -/
def conclusion_schur_gibbs_signature_complete_invertibility_forward
    (v : Omega.POM.SchurPartitionIndex → ℝ) (lam : Omega.POM.SchurPartitionIndex) : ℝ :=
  ∑ nu, (Omega.POM.schurCharacter lam nu / Omega.POM.schurWeight nu) * v nu

/-- Explicit inverse of the forward Schur-character transform. -/
def conclusion_schur_gibbs_signature_complete_invertibility_inverse
    (σ : Omega.POM.SchurPartitionIndex → ℝ) (nu : Omega.POM.SchurPartitionIndex) : ℝ :=
  ∑ lam, Omega.POM.schurCharacter lam nu * σ lam

private theorem conclusion_schur_gibbs_signature_complete_invertibility_inverse_forward
    (v : Omega.POM.SchurPartitionIndex → ℝ) (nu : Omega.POM.SchurPartitionIndex) :
    conclusion_schur_gibbs_signature_complete_invertibility_inverse
        (fun lam => conclusion_schur_gibbs_signature_complete_invertibility_forward v lam) nu =
      v nu := by
  cases nu <;>
    simp [conclusion_schur_gibbs_signature_complete_invertibility_inverse,
      conclusion_schur_gibbs_signature_complete_invertibility_forward,
      Omega.POM.sum_over_schur_partition_index, Omega.POM.schurCharacter,
      Omega.POM.schurWeight] <;>
    ring

private theorem conclusion_schur_gibbs_signature_complete_invertibility_forward_inverse
    (σ : Omega.POM.SchurPartitionIndex → ℝ) (lam : Omega.POM.SchurPartitionIndex) :
    conclusion_schur_gibbs_signature_complete_invertibility_forward
        (fun nu => conclusion_schur_gibbs_signature_complete_invertibility_inverse σ nu) lam =
      σ lam := by
  cases lam <;>
    simp [conclusion_schur_gibbs_signature_complete_invertibility_forward,
      conclusion_schur_gibbs_signature_complete_invertibility_inverse,
      Omega.POM.sum_over_schur_partition_index, Omega.POM.schurCharacter,
      Omega.POM.schurWeight] <;>
    ring

/-- Concrete statement packaging the forward Schur/Gibbs signature transform and its explicit
inverse on the `S₂` seed. -/
def conclusion_schur_gibbs_signature_complete_invertibility_statement : Prop :=
  (∀ m : ℝ,
    ∀ lam : Omega.POM.SchurPartitionIndex,
      conclusion_schur_gibbs_signature_complete_invertibility_forward
          (Omega.POM.schurCycleMonomial m) lam =
        Omega.POM.schurNormalizedChannelTrace m lam) ∧
    (∀ m : ℝ,
      ∀ nu : Omega.POM.SchurPartitionIndex,
        conclusion_schur_gibbs_signature_complete_invertibility_inverse
            (fun lam =>
              conclusion_schur_gibbs_signature_complete_invertibility_forward
                (Omega.POM.schurCycleMonomial m) lam) nu =
          Omega.POM.schurCycleMonomial m nu) ∧
    (∀ σ : Omega.POM.SchurPartitionIndex → ℝ,
      ∀ lam : Omega.POM.SchurPartitionIndex,
        conclusion_schur_gibbs_signature_complete_invertibility_forward
            (fun nu =>
              conclusion_schur_gibbs_signature_complete_invertibility_inverse σ nu) lam =
          σ lam)

/-- Paper label: `thm:conclusion-schur-gibbs-signature-complete-invertibility`. In the concrete
`S₂` Schur seed, the forward Gibbs signature is the usual weighted character transform, the
column-orthogonality calculation recovers each partition monomial from that signature, and the
same explicit formulas are two-sided inverses on the signature table. -/
theorem paper_conclusion_schur_gibbs_signature_complete_invertibility :
    conclusion_schur_gibbs_signature_complete_invertibility_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m lam
    rfl
  · intro m nu
    exact conclusion_schur_gibbs_signature_complete_invertibility_inverse_forward
      (Omega.POM.schurCycleMonomial m) nu
  · intro σ lam
    exact conclusion_schur_gibbs_signature_complete_invertibility_forward_inverse σ lam

end

end Omega.Conclusion
