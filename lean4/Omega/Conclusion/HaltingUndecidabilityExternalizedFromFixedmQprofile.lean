import Omega.Conclusion.MinLatchesLogStates
import Omega.Conclusion.ReversibleAuxBitsBudget
import Omega.Conclusion.SoftcoreFixedMQseriesRationalOgf
import Omega.Conclusion.SoftcoreSpectralScaleSeparation
import Omega.Conclusion.TemperatureKernelFreeEnergyNonapproximable

namespace Omega.Conclusion

open Omega.Zeta

/-- A fixed-`m` q-profile is finitely recoverable when its ordinary generating function is rational
with the fixed Lucas/geometric denominator package. -/
def conclusion_halting_undecidability_externalized_from_fixedm_qprofile_finite_recoverable
    {ι : Type*} [Fintype ι] (m : ℕ) (c Theta : ι → ℚ) : Prop :=
  softcoreFixedMQseriesRationalOgf m c Theta

/-- The finite q-window recovers the word-trace recurrence witness. -/
def conclusion_halting_undecidability_externalized_from_fixedm_qprofile_wordtrace_recoverable
    {ι : Type*} [Fintype ι] (m : ℕ) (c Theta : ι → ℚ) : Prop :=
  SoftcoreFixedMQrecurrenceWitness m c Theta

/-- High-q one-mode dominance is represented by the softcore spectral scale-separation wrapper. -/
def conclusion_halting_undecidability_externalized_from_fixedm_qprofile_one_mode_tail
    (q : ℕ) : Prop :=
  SoftcoreSpectralScaleSeparation q

/-- The externalized branch is witnessed by the nonapproximability theorem and the finite
binary-resource encoding used in the conclusion. -/
def conclusion_halting_undecidability_externalized_from_fixedm_qprofile_externalized : Prop :=
  conclusion_temperature_kernel_free_energy_nonapproximable_statement.{0} ∧
    Nat.clog 2 1 = 0 ∧
    Nat.clog 2 2 = 1 ∧
    Nat.clog 2 3 = 2 ∧
    Nat.clog 2 4 = 2 ∧
    Nat.clog 2 5 = 3 ∧
    Nat.clog 2 8 = 3 ∧
    Nat.clog 2 9 = 4

/-- Paper label:
`thm:conclusion-halting-undecidability-externalized-from-fixedm-qprofile`.

For each fixed `m`, the q-profile lies in the finite rational/recurrence class, its word-trace
window is recoverable, and its high-q tail is single-mode.  The undecidable component used later
therefore comes from the external halting family, recorded by the existing nonapproximability and
binary-resource interfaces. -/
theorem paper_conclusion_halting_undecidability_externalized_from_fixedm_qprofile
    {ι : Type*} [Fintype ι] (m q : ℕ) (c Theta : ι → ℚ) :
    conclusion_halting_undecidability_externalized_from_fixedm_qprofile_finite_recoverable
        m c Theta ∧
      conclusion_halting_undecidability_externalized_from_fixedm_qprofile_wordtrace_recoverable
        m c Theta ∧
      conclusion_halting_undecidability_externalized_from_fixedm_qprofile_one_mode_tail q ∧
      conclusion_halting_undecidability_externalized_from_fixedm_qprofile_externalized := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_conclusion_softcore_fixedm_qseries_rational_ogf m c Theta
  · exact paper_conclusion_softcore_fixedm_qrecurrence_annihilator m c Theta
  · exact paper_conclusion_softcore_spectral_scale_separation q
  · refine ⟨paper_conclusion_temperature_kernel_free_energy_nonapproximable, ?_⟩
    exact MinLatchesLogStates.paper_conclusion_min_latches_log_states

end Omega.Conclusion
