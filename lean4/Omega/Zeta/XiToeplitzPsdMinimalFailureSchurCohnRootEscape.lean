import Mathlib.Tactic
import Omega.Zeta.XiToeplitzDetVerblunsky

namespace Omega.Zeta

noncomputable section

/-- Concrete Schur-Cohn/Toeplitz data: a finite Toeplitz determinant recursion, a positive scalar
congruence factor for each truncation, and the first certified root-escape level. -/
structure xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data where
  toeplitz : XiToeplitzDetVerblunskyData
  schurScale : ℕ → ℝ
  schurScale_pos : ∀ m : ℕ, 0 < schurScale m
  firstEscape : ℕ
  firstEscape_isLeast : IsLeast toeplitz.failureSet firstEscape

namespace xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data

/-- The root-escape set coming from the first Verblunsky modulus with size at least one. -/
def xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_root_set
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) : Set ℕ :=
  D.toeplitz.failureSet

/-- Toeplitz bad levels, detected by nonpositive principal determinants. -/
def xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) : Set ℕ :=
  {m | D.toeplitz.toeplitzDet m ≤ 0}

/-- The scalar Schur-Cohn minor produced by the positive congruence rescaling. -/
def xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_minor
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) (m : ℕ) : ℝ :=
  D.schurScale m * D.toeplitz.toeplitzDet m

/-- Schur-Cohn bad levels, detected by nonpositive rescaled minors. -/
def xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) : Set ℕ :=
  {m | D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_minor m ≤ 0}

end xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data

open xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data

/-- The missing Schur-Cohn congruence package: positive rescaling preserves the sign of each
principal minor, so the Toeplitz and Schur-Cohn bad sets have the same inertia profile and the
least bad Toeplitz level is exactly the first root-escape level. -/
def xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_statement
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) : Prop :=
  (∀ m : ℕ,
    m ∈ D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set ↔
      m ∈ D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set) ∧
    IsLeast (D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_root_set) D.firstEscape ∧
    IsLeast (D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set)
      D.firstEscape ∧
    IsLeast (D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set)
      D.firstEscape

private lemma xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_bad_iff
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) (m : ℕ) :
    m ∈ D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set ↔
      m ∈ D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set := by
  constructor
  · intro hm
    simp [xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set,
      xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set,
      xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_minor] at hm ⊢
    by_contra hdet
    have hdet_pos : 0 < D.toeplitz.toeplitzDet m := lt_of_not_ge hdet
    have hminor_pos : 0 < D.schurScale m * D.toeplitz.toeplitzDet m := by
      exact mul_pos (D.schurScale_pos m) hdet_pos
    exact not_lt_of_ge hm hminor_pos
  · intro hm
    simpa [xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set,
      xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set,
      xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_minor] using
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (D.schurScale_pos m)) hm

/-- Paper label:
`thm:xi-toeplitz-psd-minimal-failure-schur-cohn-root-escape`. -/
theorem paper_xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape
    (D : xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_data) :
    xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_statement D := by
  have hrootLeast :
      IsLeast (D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_root_set) D.firstEscape :=
    D.firstEscape_isLeast
  have hcontrol :
      D.toeplitz.toeplitzDet D.firstEscape ≤ 0 ∧
        ∀ r < D.firstEscape, 0 < D.toeplitz.toeplitzDet r := by
    exact (paper_xi_toeplitz_det_verblunsky D.toeplitz).2 D.firstEscape hrootLeast
  have htoeplitzLeast :
      IsLeast (D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set)
        D.firstEscape := by
    refine ⟨hcontrol.1, ?_⟩
    intro m hm
    by_contra hlt
    have hpos : 0 < D.toeplitz.toeplitzDet m := hcontrol.2 m (lt_of_not_ge hlt)
    exact not_le_of_gt hpos hm
  have hschurLeast :
      IsLeast (D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_cohn_bad_set)
        D.firstEscape := by
    refine ⟨(xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_bad_iff D
        D.firstEscape).2 hcontrol.1, ?_⟩
    intro m hm
    have hm' :
        m ∈ D.xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_toeplitz_bad_set :=
      (xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_bad_iff D m).1 hm
    exact htoeplitzLeast.2 hm'
  exact ⟨xi_toeplitz_psd_minimal_failure_schur_cohn_root_escape_schur_bad_iff D,
    hrootLeast, htoeplitzLeast, hschurLeast⟩

end

end Omega.Zeta
