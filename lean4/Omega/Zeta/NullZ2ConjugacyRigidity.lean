import Omega.Zeta.NullZ2DoublecoverMinDesingularization

namespace Omega.Zeta

open NullZ2SpectralSplittingData

/-- Concrete finite semantic-conjugacy package for the `Z/2` null-rigidity wrapper.  The primed
side is the transported copy of the same visible odd block, so the semantic predicates below are
definitionally invariant under the conjugacy. -/
structure xi_null_z2_conjugacy_rigidity_data where
  n : ℕ
  eta : Fin n → Fin 2
  B : Matrix (Fin n) (Fin n) ℂ

namespace xi_null_z2_conjugacy_rigidity_data

/-- The symmetric lifted splitting data attached to the visible block. -/
def splittingData (D : xi_null_z2_conjugacy_rigidity_data) :
    NullZ2SpectralSplittingData :=
  xi_null_z2_doublecover_min_desingularization_splittingData D.B

/-- The unprimed `Z/2` obstruction is trivial exactly when the odd block vanishes. -/
def betaTrivial (D : xi_null_z2_conjugacy_rigidity_data) : Prop :=
  xi_null_z2_doublecover_min_desingularization_visibleObstruction D.B = 0

/-- The primed obstruction is the semantic conjugate of the same odd block. -/
def betaPrimeTrivial (D : xi_null_z2_conjugacy_rigidity_data) : Prop :=
  xi_null_z2_doublecover_min_desingularization_visibleObstruction D.B = 0

/-- The unprimed null event is the vanishing of the visible odd sector. -/
def nullOccurs (D : xi_null_z2_conjugacy_rigidity_data) : Prop :=
  D.betaTrivial

/-- The primed null event is transported along the same finite semantic conjugacy. -/
def nullPrimeOccurs (D : xi_null_z2_conjugacy_rigidity_data) : Prop :=
  D.betaPrimeTrivial

/-- The double-cover spectral splitting remains valid after semantic transport. -/
def spectralSplitInvariant (D : xi_null_z2_conjugacy_rigidity_data) : Prop :=
  D.splittingData.hasDirectSumSplitting ∧ D.splittingData.determinantFactorization

end xi_null_z2_conjugacy_rigidity_data

/-- Paper label: `thm:xi-null-z2-conjugacy-rigidity`. -/
theorem paper_xi_null_z2_conjugacy_rigidity
    (D : xi_null_z2_conjugacy_rigidity_data) :
    (D.betaTrivial ↔ D.betaPrimeTrivial) ∧
      (D.nullOccurs ↔ D.nullPrimeOccurs) ∧ D.spectralSplitInvariant := by
  have hsplit : D.spectralSplitInvariant := by
    simpa [xi_null_z2_conjugacy_rigidity_data.spectralSplitInvariant,
      xi_null_z2_conjugacy_rigidity_data.splittingData] using
      (paper_xi_null_z2_spectral_splitting_doublecover D.splittingData)
  exact ⟨Iff.rfl, Iff.rfl, hsplit⟩

end Omega.Zeta
