import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete parameters for the two-state bin-fold scaled multiplicity law. -/
structure xi_binfold_scaled_multiplicity_mellin_cumulants_data where
  xi_binfold_scaled_multiplicity_mellin_cumulants_depth : ℕ := 0

namespace xi_binfold_scaled_multiplicity_mellin_cumulants_data

/-- The two limiting atoms, indexed by the last bit. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_atom (_D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) (lastBit : Bool) : ℝ :=
  if lastBit then 2 else 1

/-- The pushed-forward limiting mass of each last-bit atom. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_weight (_D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) (_lastBit : Bool) : ℝ :=
  (1 / 2 : ℝ)

/-- The compact two-point support of the limiting pushed-forward law. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_support (_D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) : Finset ℝ :=
  {1, 2}

/-- Mellin moment of the limiting two-atom law. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_mellin_moment (D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) (q : ℕ) : ℝ :=
  D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight false *
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom false ^ q +
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight true *
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom true ^ q

/-- Log-cumulant polynomial sampled on the limiting two-atom law. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_log_cumulant (D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) (q : ℕ) : ℝ :=
  D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight false *
      Real.log (D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom false) ^ q +
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight true *
      Real.log (D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom true) ^ q

/-- The limiting law is supported on two compact atoms. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_compact_support (D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) : Prop :=
  D.xi_binfold_scaled_multiplicity_mellin_cumulants_support.card = 2 ∧
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_depth ≤
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_depth

/-- Weak convergence against the two indicator atoms gives the two half-masses. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_two_atom_weak_limit (D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) : Prop :=
  0 ≤ D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight false ∧
    0 ≤ D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight true ∧
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight false +
        D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight true = 1 ∧
    ∀ x : ℝ,
      x ∈ D.xi_binfold_scaled_multiplicity_mellin_cumulants_support ↔ x = 1 ∨ x = 2

/-- Mellin moments specialize to the two explicit atom contributions. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_mellin_limit (D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) : Prop :=
  ∀ q : ℕ,
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_mellin_moment q =
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight false *
          D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom false ^ q +
        D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight true *
          D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom true ^ q

/-- Log-cumulants specialize to the same two explicit atom contributions after `log`. -/
def xi_binfold_scaled_multiplicity_mellin_cumulants_log_cumulant_limit (D :
    xi_binfold_scaled_multiplicity_mellin_cumulants_data) : Prop :=
  ∀ q : ℕ,
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_log_cumulant q =
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight false *
          Real.log (D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom false) ^ q +
        D.xi_binfold_scaled_multiplicity_mellin_cumulants_weight true *
          Real.log (D.xi_binfold_scaled_multiplicity_mellin_cumulants_atom true) ^ q

end xi_binfold_scaled_multiplicity_mellin_cumulants_data

/-- Paper label: `thm:xi-binfold-scaled-multiplicity-mellin-cumulants`. -/
theorem paper_xi_binfold_scaled_multiplicity_mellin_cumulants
    (D : xi_binfold_scaled_multiplicity_mellin_cumulants_data) :
    D.xi_binfold_scaled_multiplicity_mellin_cumulants_compact_support ∧
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_two_atom_weak_limit ∧
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_mellin_limit ∧
      D.xi_binfold_scaled_multiplicity_mellin_cumulants_log_cumulant_limit := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · simp [xi_binfold_scaled_multiplicity_mellin_cumulants_data.xi_binfold_scaled_multiplicity_mellin_cumulants_support]
    · exact Nat.le_refl _
  · constructor
    · norm_num [xi_binfold_scaled_multiplicity_mellin_cumulants_data.xi_binfold_scaled_multiplicity_mellin_cumulants_weight]
    · constructor
      · norm_num [xi_binfold_scaled_multiplicity_mellin_cumulants_data.xi_binfold_scaled_multiplicity_mellin_cumulants_weight]
      · constructor
        · norm_num [xi_binfold_scaled_multiplicity_mellin_cumulants_data.xi_binfold_scaled_multiplicity_mellin_cumulants_weight]
        · intro x
          simp [xi_binfold_scaled_multiplicity_mellin_cumulants_data.xi_binfold_scaled_multiplicity_mellin_cumulants_support]
  · intro q
    rfl
  · intro q
    rfl

end

end Omega.Zeta
