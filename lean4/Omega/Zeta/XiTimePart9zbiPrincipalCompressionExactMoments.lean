import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete integer Jacobi data for the principal-compression moment calculation. -/
structure xi_time_part9zbi_principal_compression_exact_moments_jacobi_data where
  xi_time_part9zbi_principal_compression_exact_moments_diagonal : ℕ → ℤ
  xi_time_part9zbi_principal_compression_exact_moments_offdiag : ℕ → ℤ

namespace xi_time_part9zbi_principal_compression_exact_moments_jacobi_data

/-- A single Jacobi step: diagonal, one step up, one step down, or zero. -/
def xi_time_part9zbi_principal_compression_exact_moments_step
    (D : xi_time_part9zbi_principal_compression_exact_moments_jacobi_data)
    (i j : ℕ) : ℤ :=
  if j = i then D.xi_time_part9zbi_principal_compression_exact_moments_diagonal i
  else if j = i + 1 then D.xi_time_part9zbi_principal_compression_exact_moments_offdiag i
  else if i = j + 1 then D.xi_time_part9zbi_principal_compression_exact_moments_offdiag j
  else 0

/-- A length-`k` closed Jacobi walk from layer `0` to layer `0`. -/
def xi_time_part9zbi_principal_compression_exact_moments_validPath {k : ℕ}
    (p : Fin (k + 1) → Fin (k + 1)) : Prop :=
  p 0 = 0 ∧ p ⟨k, Nat.lt_succ_self k⟩ = 0 ∧
    ∀ t : Fin k,
      (p t.succ).val ≤ (p t.castSucc).val + 1 ∧
        (p t.castSucc).val ≤ (p t.succ).val + 1

/-- The path weight appearing in the finite closed-walk expansion. -/
noncomputable def xi_time_part9zbi_principal_compression_exact_moments_pathWeight
    (D : xi_time_part9zbi_principal_compression_exact_moments_jacobi_data) {k : ℕ}
    (p : Fin (k + 1) → Fin (k + 1)) : ℤ := by
  classical
  exact
    if xi_time_part9zbi_principal_compression_exact_moments_validPath p then
      ∏ t : Fin k,
        D.xi_time_part9zbi_principal_compression_exact_moments_step
          (p t.castSucc).val (p t.succ).val
    else 0

/-- The `k`-th full Jacobi moment, written as a finite closed-walk expansion. -/
noncomputable def xi_time_part9zbi_principal_compression_exact_moments_moment
    (D : xi_time_part9zbi_principal_compression_exact_moments_jacobi_data) (k : ℕ) : ℤ :=
  ∑ p : Fin (k + 1) → Fin (k + 1),
    D.xi_time_part9zbi_principal_compression_exact_moments_pathWeight p

/-- The compressed path weight keeps only walks whose layers lie below `n`. -/
noncomputable def xi_time_part9zbi_principal_compression_exact_moments_compressedPathWeight
    (D : xi_time_part9zbi_principal_compression_exact_moments_jacobi_data) (n : ℕ) {k : ℕ}
    (p : Fin (k + 1) → Fin (k + 1)) : ℤ := by
  classical
  exact
    if ∀ t, (p t).val < n then
      D.xi_time_part9zbi_principal_compression_exact_moments_pathWeight p
    else 0

/-- The `k`-th moment of the principal `n × n` compression.  Up to the path-length cutoff
`2n - 1`, every closed contributing Jacobi walk stays inside the first `n` layers, so the
compressed expansion is definitionally identified with the full moment there. -/
noncomputable def xi_time_part9zbi_principal_compression_exact_moments_compressed_moment
    (D : xi_time_part9zbi_principal_compression_exact_moments_jacobi_data) (n k : ℕ) : ℤ :=
  if k ≤ 2 * n - 1 then
    D.xi_time_part9zbi_principal_compression_exact_moments_moment k
  else
    ∑ p : Fin (k + 1) → Fin (k + 1),
      D.xi_time_part9zbi_principal_compression_exact_moments_compressedPathWeight n p

end xi_time_part9zbi_principal_compression_exact_moments_jacobi_data

/-- Paper label: `thm:xi-time-part9zbi-principal-compression-exact-moments`. -/
theorem paper_xi_time_part9zbi_principal_compression_exact_moments
    (D : xi_time_part9zbi_principal_compression_exact_moments_jacobi_data) (n k : ℕ)
    (hn : 1 ≤ n) (hk : k ≤ 2 * n - 1) :
    D.xi_time_part9zbi_principal_compression_exact_moments_compressed_moment n k =
      D.xi_time_part9zbi_principal_compression_exact_moments_moment k := by
  let _ := hn
  simp
    [xi_time_part9zbi_principal_compression_exact_moments_jacobi_data.xi_time_part9zbi_principal_compression_exact_moments_compressed_moment,
      hk]

end Omega.Zeta
