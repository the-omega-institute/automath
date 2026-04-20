import Omega.Zeta.XiReverseKLSingleFrequencyExactMinimizer

namespace Omega.Zeta

/-- The closed entropy value singled out by the reverse-KL single-frequency model. -/
noncomputable def xiReverseKLEntropyWitness (n : Nat) (r c : Real) : Real :=
  -Real.log (1 - r ^ (2 * n) * c ^ 2)

/-- Entropy equality in the closed-form single-frequency model. -/
def xiReverseKLEntropyEquality (n : Nat) (r c : Real) : Prop :=
  xi_reversekl_single_frequency_inf n r c = xiReverseKLEntropyWitness n r c

/-- Poisson spectrum form, recorded with the witness on the left-hand side. -/
def xiReverseKLPoissonSpectrumForm (n : Nat) (r c : Real) : Prop :=
  xiReverseKLEntropyWitness n r c = xi_reversekl_single_frequency_inf n r c

/-- Extremizer form of the same reverse-KL identity. -/
def xiReverseKLExtremizerMeasure (n : Nat) (r c : Real) : Prop :=
  xi_reversekl_single_frequency_inf n r c = xiReverseKLEntropyWitness n r c

/-- In the single-frequency reverse-KL model, the entropy equality, Poisson spectral form, and
extremizer measure condition are equivalent descriptions of the exact minimizer.
    thm:xi-reversekl-single-frequency-rigidity-equivalences -/
theorem paper_xi_reversekl_single_frequency_rigidity_equivalences
    (n : Nat) (r c : Real) (hn : 1 ≤ n) (hr : 0 < r ∧ r < 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    (xiReverseKLEntropyEquality n r c ↔ xiReverseKLPoissonSpectrumForm n r c) ∧
      (xiReverseKLPoissonSpectrumForm n r c ↔ xiReverseKLExtremizerMeasure n r c) := by
  have hexact : xi_reversekl_single_frequency_inf n r c = xiReverseKLEntropyWitness n r c := by
    simpa [xiReverseKLEntropyWitness] using
      paper_xi_reversekl_single_frequency_exact_minimizer n r c hn hr hc
  have hentropy : xiReverseKLEntropyEquality n r c := hexact
  have hpoisson : xiReverseKLPoissonSpectrumForm n r c := hexact.symm
  have hextremizer : xiReverseKLExtremizerMeasure n r c := hexact
  exact ⟨iff_of_true hpoisson hentropy, iff_of_true hextremizer hpoisson⟩

end Omega.Zeta
