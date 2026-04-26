import Omega.Folding.FoldInfoNCELossSpectrumIdentifiability
import Omega.Folding.OracleCapacityWatataniIndexTraceFormula
import Omega.Folding.Window6
import Omega.OperatorAlgebra.FoldWatataniIndexMoments
import Omega.POM.MacroMomentVsMicroPrimeRegisterCertificateSeparation
import Omega.POM.OracleCapacityStieltjesInversionMellin

namespace Omega.Folding

open scoped BigOperators

/-- Paper label: `cor:fold-infonce-loss-spectrum-determines-index-tqft-capacity`. Once the
triangular InfoNCE loss spectrum determines the multiplicity power sums, the existing fold
formulas immediately recover the traced Watatani moments, the oracle-capacity package, the basic
TQFT partition functions, and the chapter's prime-register certificate consequence. -/
theorem paper_fold_infonce_loss_spectrum_determines_index_tqft_capacity
    {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq Ω] [DecidableEq X]
    (fold : Ω → X) (m N : Nat) (beta : Nat → Nat → Real)
    (spectrumPowerSum lossPowerSum : Nat → Real) (hcard : Fintype.card Ω = 2 ^ m)
    (hdiag : ∀ K, 2 ≤ K → K ≤ N → beta K K != 0)
    (hloss : ∀ K, 2 ≤ K → K ≤ N ->
      Finset.sum (Finset.Icc 2 K) (fun q => beta K q * spectrumPowerSum q) =
        Finset.sum (Finset.Icc 2 K) (fun q => beta K q * lossPowerSum q))
    (hspectrum : ∀ q, 2 ≤ q → q ≤ N →
      spectrumPowerSum q = ∑ x : X, (Fintype.card {ω : Ω // fold ω = x} : ℝ) ^ q) :
    (∀ q, 2 ≤ q → q ≤ N →
      lossPowerSum q = ∑ x : X, (Fintype.card {ω : Ω // fold ω = x} : ℝ) ^ q) ∧
      Omega.OperatorAlgebra.FoldWatataniIndexMomentsFormula fold m 1 ∧
      fold_oracle_watatani_index_trace_formula_statement fold 1 ∧
      Omega.POM.oracle_capacity_stieltjes_mellin_package fold ∧
      (∑ x : Omega.X m, (Omega.X.fiberMultiplicity x) ^ 2 = Omega.momentSum 2 m) ∧
      (∑ x : Omega.X m, (Omega.X.fiberMultiplicity x) ^ 0 = Nat.fib (m + 2)) ∧
      Omega.POM.MacroVsMicroPrimeRegisterSeparation 2 := by
  have hrecover :=
    paper_fold_infonce_loss_spectrum_identifiability N beta spectrumPowerSum lossPowerSum
      hdiag hloss
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hqN
    rw [← hrecover q hq hqN]
    exact hspectrum q hq hqN
  · exact Omega.OperatorAlgebra.paper_op_algebra_fold_watatani_index_moments fold m 1 hcard
  · exact paper_fold_oracle_watatani_index_trace_formula fold 1
  · exact Omega.POM.paper_pom_oracle_capacity_stieltjes_inversion_mellin fold
  · exact Omega.tqft_sphere_eq_momentSum_two m
  · exact Omega.tqft_torus_eq_card m
  · exact Omega.POM.paper_pom_macro_moment_vs_micro_prime_register_certificate_separation 2
      (by decide)

end Omega.Folding
