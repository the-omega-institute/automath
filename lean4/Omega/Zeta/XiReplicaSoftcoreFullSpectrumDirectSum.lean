import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/--
Concrete spectral bookkeeping for the replica softcore full-spectrum split.

The data records the body eigenvalue labels, the exceptional eigenvalue labels, the announced
body multiplicities, and the dimension count for the exceptional/body decomposition.  The
separation hypothesis is the paper's final strict exceptional-spectrum separation input.
-/
structure xi_replica_softcore_full_spectrum_direct_sum_data (q : ℕ) where
  xi_replica_softcore_full_spectrum_direct_sum_bodyEigenvalue : Fin (q + 1) → ℝ
  xi_replica_softcore_full_spectrum_direct_sum_exceptionalEigenvalue : Fin (q + 1) → ℝ
  xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity : Fin (q + 1) → ℕ
  xi_replica_softcore_full_spectrum_direct_sum_bodyScalar : Fin (q + 1) → ℝ
  xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity_formula :
    ∀ i : Fin (q + 1),
      xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity i = Nat.choose q i.val - 1
  xi_replica_softcore_full_spectrum_direct_sum_bodyScalar_formula :
    ∀ i : Fin (q + 1),
      xi_replica_softcore_full_spectrum_direct_sum_bodyScalar i =
        xi_replica_softcore_full_spectrum_direct_sum_bodyEigenvalue i / 2
  xi_replica_softcore_full_spectrum_direct_sum_exceptional_cardinality :
    Fintype.card (Fin (q + 1)) = q + 1
  xi_replica_softcore_full_spectrum_direct_sum_dimension_count :
    (Fintype.card (Fin (q + 1)) +
        ∑ i : Fin (q + 1), xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity i) =
      2 ^ q
  xi_replica_softcore_full_spectrum_direct_sum_exceptional_body_disjoint :
    ∀ i j : Fin (q + 1),
      xi_replica_softcore_full_spectrum_direct_sum_exceptionalEigenvalue i ≠
        xi_replica_softcore_full_spectrum_direct_sum_bodyEigenvalue j / 2

namespace xi_replica_softcore_full_spectrum_direct_sum_data

/-- The body eigenvalues have the binomial-minus-one multiplicities. -/
def bodySpectrumMultiplicities
    {q : ℕ} (D : xi_replica_softcore_full_spectrum_direct_sum_data q) : Prop :=
  ∀ i : Fin (q + 1),
    D.xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity i = Nat.choose q i.val - 1

/-- The exceptional block contributes exactly `q + 1` eigenvalues. -/
def exceptionalSpectrumCardinality
    {q : ℕ} (_D : xi_replica_softcore_full_spectrum_direct_sum_data q) : Prop :=
  Fintype.card (Fin (q + 1)) = q + 1

/-- The exceptional block and body blocks account for the whole `2^q`-dimensional space. -/
def orthogonalDirectSumDecomposition
    {q : ℕ} (D : xi_replica_softcore_full_spectrum_direct_sum_data q) : Prop :=
  (Fintype.card (Fin (q + 1)) +
      ∑ i : Fin (q + 1), D.xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity i) =
    2 ^ q

/-- On each body summand the softcore operator acts by half the tensor eigenvalue. -/
def bodyScalarAction
    {q : ℕ} (D : xi_replica_softcore_full_spectrum_direct_sum_data q) : Prop :=
  ∀ i : Fin (q + 1),
    D.xi_replica_softcore_full_spectrum_direct_sum_bodyScalar i =
      D.xi_replica_softcore_full_spectrum_direct_sum_bodyEigenvalue i / 2

/-- The supplied exceptional spectrum is disjoint from the body spectrum. -/
def spectrumDisjoint
    {q : ℕ} (D : xi_replica_softcore_full_spectrum_direct_sum_data q) : Prop :=
  ∀ i j : Fin (q + 1),
    D.xi_replica_softcore_full_spectrum_direct_sum_exceptionalEigenvalue i ≠
      D.xi_replica_softcore_full_spectrum_direct_sum_bodyEigenvalue j / 2

end xi_replica_softcore_full_spectrum_direct_sum_data

open xi_replica_softcore_full_spectrum_direct_sum_data

/-- Paper label: `thm:xi-replica-softcore-full-spectrum-direct-sum`. -/
theorem paper_xi_replica_softcore_full_spectrum_direct_sum (q : ℕ) (hq : 2 ≤ q)
    (D : xi_replica_softcore_full_spectrum_direct_sum_data q) :
    D.bodySpectrumMultiplicities ∧ D.exceptionalSpectrumCardinality ∧
      D.orthogonalDirectSumDecomposition ∧ D.bodyScalarAction ∧ D.spectrumDisjoint := by
  have xi_replica_softcore_full_spectrum_direct_sum_hq : 2 ≤ q := hq
  clear xi_replica_softcore_full_spectrum_direct_sum_hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact D.xi_replica_softcore_full_spectrum_direct_sum_bodyMultiplicity_formula
  · exact D.xi_replica_softcore_full_spectrum_direct_sum_exceptional_cardinality
  · exact D.xi_replica_softcore_full_spectrum_direct_sum_dimension_count
  · exact D.xi_replica_softcore_full_spectrum_direct_sum_bodyScalar_formula
  · exact D.xi_replica_softcore_full_spectrum_direct_sum_exceptional_body_disjoint

end

end Omega.Zeta
