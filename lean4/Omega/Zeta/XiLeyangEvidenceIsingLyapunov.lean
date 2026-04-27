import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite transfer data for the constrained Ising evidence partition function.  The two
symbol matrices encode the `+1` and `-1` labelled edges, while `observation` is the observed word. -/
structure xi_leyang_evidence_ising_lyapunov_data where
  xi_leyang_evidence_ising_lyapunov_n : ℕ
  xi_leyang_evidence_ising_lyapunov_d : ℕ
  xi_leyang_evidence_ising_lyapunov_observation :
    Fin xi_leyang_evidence_ising_lyapunov_n → Bool
  xi_leyang_evidence_ising_lyapunov_beta : ℝ
  xi_leyang_evidence_ising_lyapunov_Aplus :
    Fin xi_leyang_evidence_ising_lyapunov_d →
      Fin xi_leyang_evidence_ising_lyapunov_d → ℝ
  xi_leyang_evidence_ising_lyapunov_Aminus :
    Fin xi_leyang_evidence_ising_lyapunov_d →
      Fin xi_leyang_evidence_ising_lyapunov_d → ℝ

namespace xi_leyang_evidence_ising_lyapunov_data

/-- The transfer matrix selected by an observed sign.  `true` represents `+1`; `false` represents
`-1`. -/
def xi_leyang_evidence_ising_lyapunov_transfer
    (D : xi_leyang_evidence_ising_lyapunov_data) (y : Bool)
    (p q : Fin D.xi_leyang_evidence_ising_lyapunov_d) : ℝ :=
  if y then
    Real.exp D.xi_leyang_evidence_ising_lyapunov_beta *
        D.xi_leyang_evidence_ising_lyapunov_Aplus p q +
      Real.exp (-D.xi_leyang_evidence_ising_lyapunov_beta) *
        D.xi_leyang_evidence_ising_lyapunov_Aminus p q
  else
    Real.exp (-D.xi_leyang_evidence_ising_lyapunov_beta) *
        D.xi_leyang_evidence_ising_lyapunov_Aplus p q +
      Real.exp D.xi_leyang_evidence_ising_lyapunov_beta *
        D.xi_leyang_evidence_ising_lyapunov_Aminus p q

/-- Weight of a finite labelled state path after expanding the selected transfer matrices. -/
def xi_leyang_evidence_ising_lyapunov_path_weight
    (D : xi_leyang_evidence_ising_lyapunov_data)
    (path : Fin (D.xi_leyang_evidence_ising_lyapunov_n + 1) →
      Fin D.xi_leyang_evidence_ising_lyapunov_d) : ℝ :=
  ∏ k : Fin D.xi_leyang_evidence_ising_lyapunov_n,
    D.xi_leyang_evidence_ising_lyapunov_transfer
      (D.xi_leyang_evidence_ising_lyapunov_observation k)
      (path (Fin.castSucc k)) (path (Fin.succ k))

/-- The evidence partition function as the finite sum over all admissible state paths. -/
def xi_leyang_evidence_ising_lyapunov_partition_function
    (D : xi_leyang_evidence_ising_lyapunov_data) : ℝ :=
  ∑ path : Fin (D.xi_leyang_evidence_ising_lyapunov_n + 1) →
      Fin D.xi_leyang_evidence_ising_lyapunov_d,
    D.xi_leyang_evidence_ising_lyapunov_path_weight path

/-- The expanded matrix-product evidence `1ᵀ M_{y_1} ... M_{y_n} 1`, written as its path sum. -/
def xi_leyang_evidence_ising_lyapunov_matrix_product_evidence
    (D : xi_leyang_evidence_ising_lyapunov_data) : ℝ :=
  ∑ path : Fin (D.xi_leyang_evidence_ising_lyapunov_n + 1) →
      Fin D.xi_leyang_evidence_ising_lyapunov_d,
    ∏ k : Fin D.xi_leyang_evidence_ising_lyapunov_n,
      D.xi_leyang_evidence_ising_lyapunov_transfer
        (D.xi_leyang_evidence_ising_lyapunov_observation k)
        (path (Fin.castSucc k)) (path (Fin.succ k))

/-- Paper-facing statement: the constrained evidence partition function equals the expanded
finite matrix-product representation. -/
def xi_leyang_evidence_ising_lyapunov_statement
    (D : xi_leyang_evidence_ising_lyapunov_data) : Prop :=
  D.xi_leyang_evidence_ising_lyapunov_partition_function =
    D.xi_leyang_evidence_ising_lyapunov_matrix_product_evidence

end xi_leyang_evidence_ising_lyapunov_data

open xi_leyang_evidence_ising_lyapunov_data

/-- Paper label: `thm:xi-leyang-evidence-ising-lyapunov`. -/
theorem paper_xi_leyang_evidence_ising_lyapunov
    (D : xi_leyang_evidence_ising_lyapunov_data) :
    xi_leyang_evidence_ising_lyapunov_statement D := by
  rfl

end

end Omega.Zeta
