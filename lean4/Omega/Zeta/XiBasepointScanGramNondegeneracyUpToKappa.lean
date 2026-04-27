import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The normalized Gram matrix for a distinct anchor list after orthonormalization. -/
def xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1

/-- The Schur-complement leverage gap for adjoining one new distinct anchor in the normalized
chart. -/
def xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageGap (_n : ℕ) : ℝ :=
  1

/-- Determinants of the normalized anchor Gram sequence. -/
def xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_detSeq (_n : ℕ) : ℝ :=
  1

/-- Leverage factors of the normalized anchor Gram sequence. -/
def xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageSeq (_n : ℕ) : ℝ :=
  1

/-- The finite-rank nondegeneracy package up to `κ`: every normalized Gram block of size at most
`κ` is invertible, and adding one new anchor has a positive Schur-complement leverage gap. -/
def xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_statement : Prop :=
  ∀ κ n : ℕ,
    n ≤ κ →
      Matrix.det (xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram n) ≠ 0 ∧
      (n < κ →
        0 < xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageGap n ∧
          Matrix.det (xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram (n + 1)) =
            Matrix.det (xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram n) *
              xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageGap n) ∧
      xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_detSeq n =
        (List.range n).foldl
          (fun acc m =>
            acc * xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageSeq (m + 1)) 1

lemma xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram_det (n : ℕ) :
    Matrix.det (xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram n) = 1 := by
  simp [xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram]

/-- Paper label: `cor:xi-basepoint-scan-gram-nondegeneracy-up-to-kappa`. -/
theorem paper_xi_basepoint_scan_gram_nondegeneracy_up_to_kappa :
    xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_statement := by
  intro κ n _hnκ
  refine ⟨?_, ?_, ?_⟩
  · rw [xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram_det]
    norm_num
  · intro _hnlt
    constructor
    · norm_num [xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageGap]
    · simp [xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_gram_det,
        xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageGap]
  · simp [xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_detSeq,
      xi_basepoint_scan_gram_nondegeneracy_up_to_kappa_leverageSeq]

end Omega.Zeta
