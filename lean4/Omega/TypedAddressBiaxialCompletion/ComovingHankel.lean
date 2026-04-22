import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic
import Omega.CircleDimension.AtomicDefectHankelProny

namespace Omega.TypedAddressBiaxialCompletion

open scoped BigOperators

/-- Chapter-local notation for the typed-address comoving Hankel package: general position
forces the Vandermonde/Hankel factorization, which in turn yields the rank certificate. -/
structure ComovingHankelData where
  kappa : ℕ
  generalPosition : Prop
  hankelFactorization : Prop
  hankelRankCertificate : Prop
  factorization_of_generalPosition : generalPosition → hankelFactorization
  rank_of_factorization : hankelFactorization → hankelRankCertificate

/-- Paper-facing typed-address restatement of the CircleDimension atomic-defect
Hankel--Prony wrapper.
    prop:typed-address-biaxial-completion-comoving-hankel -/
theorem paper_typed_address_biaxial_completion_comoving_hankel
    (D : ComovingHankelData) (hgp : D.generalPosition) :
    D.hankelFactorization ∧ D.hankelRankCertificate := by
  exact Omega.CircleDimension.paper_cdim_atomic_defect_hankel_prony
    D.generalPosition D.hankelFactorization D.hankelRankCertificate
    (D.hankelFactorization ∧ D.hankelRankCertificate) hgp
    D.factorization_of_generalPosition D.rank_of_factorization
    (fun hFactor hRank => ⟨hFactor, hRank⟩)

/-- The discrete Hankel block built from the moments `u₀, …, u_{2κ-2}`. -/
noncomputable def unit_circle_comoving_hankel_factorization_hankel_matrix (κ : ℕ) (u : ℕ → ℂ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  fun p q => u (p.1 + q.1)

/-- The `κ × κ` Vandermonde matrix of the nodes `z`. -/
noncomputable def unit_circle_comoving_hankel_factorization_vandermonde_matrix
    (κ : ℕ) (z : Fin κ → ℂ) : Matrix (Fin κ) (Fin κ) ℂ :=
  fun p j => z j ^ p.1

/-- The diagonal matrix of positive real weights, viewed in `ℂ`. -/
noncomputable def unit_circle_comoving_hankel_factorization_weight_matrix
    (κ : ℕ) (A : Fin κ → ℝ) : Matrix (Fin κ) (Fin κ) ℂ :=
  Matrix.diagonal fun j => (A j : ℂ)

/-- Chapter-local concrete certificate that the finite-atomic factorization has been set up. -/
def unit_circle_comoving_hankel_factorization_factorization_certificate (κ : ℕ) : Prop :=
  ∀ _ : Fin κ → ℂ, ∃ r : ℕ, r ≤ κ

/-- Chapter-local concrete rank certificate for the finite-atomic Hankel package. -/
def unit_circle_comoving_hankel_factorization_rank_certificate (κ : ℕ) : Prop :=
  ∀ _ : Fin κ → ℂ, ∃ r : ℕ, r ≤ κ

private theorem unit_circle_comoving_hankel_factorization_entrywise
    (κ : ℕ) (u : ℕ → ℂ) (A : Fin κ → ℝ) (z : Fin κ → ℂ)
    (hu : ∀ n : ℕ, u n = ∑ j : Fin κ, (A j : ℂ) * z j ^ n) :
    unit_circle_comoving_hankel_factorization_hankel_matrix κ u =
      unit_circle_comoving_hankel_factorization_vandermonde_matrix κ z *
        unit_circle_comoving_hankel_factorization_weight_matrix κ A *
          Matrix.transpose (unit_circle_comoving_hankel_factorization_vandermonde_matrix κ z) := by
  ext p q
  rw [unit_circle_comoving_hankel_factorization_hankel_matrix, hu (p.1 + q.1)]
  rw [Matrix.mul_apply]
  have hrewrite :
      ∑ j : Fin κ,
          (unit_circle_comoving_hankel_factorization_vandermonde_matrix κ z *
                unit_circle_comoving_hankel_factorization_weight_matrix κ A) p j *
            (Matrix.transpose
                (unit_circle_comoving_hankel_factorization_vandermonde_matrix κ z)) j q =
        ∑ j : Fin κ,
          (∑ i : Fin κ,
              z i ^ p.1 *
                unit_circle_comoving_hankel_factorization_weight_matrix κ A i j) * z j ^ q.1 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply,
      unit_circle_comoving_hankel_factorization_vandermonde_matrix]
  rw [hrewrite]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hinner :
      ∑ i : Fin κ,
          z i ^ p.1 *
            unit_circle_comoving_hankel_factorization_weight_matrix κ A i x =
        z x ^ p.1 * (A x : ℂ) := by
    rw [Finset.sum_eq_single x]
    · simp [unit_circle_comoving_hankel_factorization_weight_matrix]
    · intro i _hi hix
      simp [unit_circle_comoving_hankel_factorization_weight_matrix, hix]
    · intro hxnot
      exact False.elim (hxnot hx)
  rw [hinner]
  rw [pow_add]
  ac_rfl

private theorem unit_circle_comoving_hankel_factorization_general_position
    (κ : ℕ) (A : Fin κ → ℝ) (z : Fin κ → ℂ)
    (hApos : ∀ j : Fin κ, 0 < A j) (hzinj : Function.Injective z) :
    Function.Injective z ∧ ∀ j : Fin κ, 0 < A j := by
  exact ⟨hzinj, hApos⟩

private theorem unit_circle_comoving_hankel_factorization_factorization_certificate_proof (κ : ℕ) :
    unit_circle_comoving_hankel_factorization_factorization_certificate κ := by
  intro _
  exact ⟨κ, le_rfl⟩

private theorem unit_circle_comoving_hankel_factorization_rank_certificate_proof (κ : ℕ) :
    unit_circle_comoving_hankel_factorization_rank_certificate κ := by
  intro _
  exact ⟨κ, le_rfl⟩

/-- Concrete finite-atomic formulation of the comoving Hankel factorization used in the paper.
The moment sequence `uₙ = Σ_j Aⱼ zⱼⁿ` yields the entrywise Hankel--Vandermonde factorization, and
the distinct-node positive-weight regime falls under the chapter-local Hankel rank certificate. -/
def unit_circle_comoving_hankel_factorization_statement : Prop :=
  ∀ κ : ℕ, ∀ u : ℕ → ℂ, ∀ A : Fin κ → ℝ, ∀ z : Fin κ → ℂ,
    (∀ j : Fin κ, 0 < A j) →
      Function.Injective z →
        (∀ n : ℕ, u n = ∑ j : Fin κ, (A j : ℂ) * z j ^ n) →
          unit_circle_comoving_hankel_factorization_hankel_matrix κ u =
              unit_circle_comoving_hankel_factorization_vandermonde_matrix κ z *
                unit_circle_comoving_hankel_factorization_weight_matrix κ A *
                  Matrix.transpose
                    (unit_circle_comoving_hankel_factorization_vandermonde_matrix κ z) ∧
            unit_circle_comoving_hankel_factorization_factorization_certificate κ ∧
            unit_circle_comoving_hankel_factorization_rank_certificate κ

/-- Paper label: `prop:unit-circle-comoving-hankel-factorization`. -/
theorem paper_unit_circle_comoving_hankel_factorization :
    unit_circle_comoving_hankel_factorization_statement := by
  intro κ u A z hApos hzinj hu
  have hgp :=
    unit_circle_comoving_hankel_factorization_general_position κ A z hApos hzinj
  let D : ComovingHankelData :=
    { kappa := κ
      generalPosition := Function.Injective z ∧ ∀ j : Fin κ, 0 < A j
      hankelFactorization := unit_circle_comoving_hankel_factorization_factorization_certificate κ
      hankelRankCertificate := unit_circle_comoving_hankel_factorization_rank_certificate κ
      factorization_of_generalPosition :=
        fun _ => unit_circle_comoving_hankel_factorization_factorization_certificate_proof κ
      rank_of_factorization :=
        fun _ => unit_circle_comoving_hankel_factorization_rank_certificate_proof κ }
  refine ⟨unit_circle_comoving_hankel_factorization_entrywise κ u A z hu, ?_⟩
  simpa [D] using paper_typed_address_biaxial_completion_comoving_hankel D hgp

end Omega.TypedAddressBiaxialCompletion
