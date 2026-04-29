import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldEntropy

namespace Omega.POM

/-- Concrete coding data for the microcanonical description-length lower bound. The map `code`
is an injective code from the fold classes into binary words of length `bitLength`, represented by
`Fin (2 ^ bitLength)`. The entropy hypothesis records the Stirling/asymptotic lower estimate to be
transported through the finite pigeonhole bound. -/
structure pom_microcanonical_fold_description_length_lower_bound_data where
  foldAlphabet : Type
  foldFintype : Fintype foldAlphabet
  foldDecidableEq : DecidableEq foldAlphabet
  multiplicity : foldAlphabet → ℕ
  totalMass_positive :
    letI : Fintype foldAlphabet := foldFintype
    0 < microcanonicalTotalMass multiplicity
  bitLength : ℕ
  code :
    letI : Fintype foldAlphabet := foldFintype
    letI : DecidableEq foldAlphabet := foldDecidableEq
    Fin (microcanonicalFoldClassCount multiplicity) → Fin (2 ^ bitLength)
  code_injective : Function.Injective code
  entropyRemainder : ℝ
  entropy_log_lower :
    letI : Fintype foldAlphabet := foldFintype
    letI : DecidableEq foldAlphabet := foldDecidableEq
    ((microcanonicalTotalMass multiplicity : ℝ) *
          microcanonicalFoldShannonEntropy multiplicity) /
        Real.log 2 -
      entropyRemainder ≤ (Nat.clog 2 (microcanonicalFoldClassCount multiplicity) : ℝ)

namespace pom_microcanonical_fold_description_length_lower_bound_data

/-- The concrete number of microcanonical fold classes. -/
noncomputable def pom_microcanonical_fold_description_length_lower_bound_classCount
    (D : pom_microcanonical_fold_description_length_lower_bound_data) : ℕ :=
  letI : Fintype D.foldAlphabet := D.foldFintype
  letI : DecidableEq D.foldAlphabet := D.foldDecidableEq
  microcanonicalFoldClassCount D.multiplicity

/-- The main entropy term, measured in bits, with the recorded asymptotic remainder subtracted. -/
noncomputable def pom_microcanonical_fold_description_length_lower_bound_entropyBits
    (D : pom_microcanonical_fold_description_length_lower_bound_data) : ℝ :=
  letI : Fintype D.foldAlphabet := D.foldFintype
  letI : DecidableEq D.foldAlphabet := D.foldDecidableEq
  ((microcanonicalTotalMass D.multiplicity : ℝ) *
        microcanonicalFoldShannonEntropy D.multiplicity) /
      Real.log 2 -
    D.entropyRemainder

/-- Pigeonhole lower bound: an injective binary code needs at least the binary ceiling logarithm
of the fold-class count. -/
def bit_lower_bound (D : pom_microcanonical_fold_description_length_lower_bound_data) : Prop :=
  Nat.clog 2 D.pom_microcanonical_fold_description_length_lower_bound_classCount ≤ D.bitLength

/-- Entropy-asymptotic lower bound transferred from the fold entropy estimate. -/
noncomputable def asymptotic_bit_lower_bound
    (D : pom_microcanonical_fold_description_length_lower_bound_data) : Prop :=
  D.pom_microcanonical_fold_description_length_lower_bound_entropyBits ≤ (D.bitLength : ℝ)

end pom_microcanonical_fold_description_length_lower_bound_data

open pom_microcanonical_fold_description_length_lower_bound_data

/-- Paper label: `cor:pom-microcanonical-fold-description-length-lower-bound`. An injective code
from all microcanonical fold classes into `2^L` codewords forces `ceil(log₂ classCount) ≤ L`; the
recorded entropy lower estimate then gives the asymptotic bit lower bound. -/
theorem paper_pom_microcanonical_fold_description_length_lower_bound
    (D : pom_microcanonical_fold_description_length_lower_bound_data) :
    D.bit_lower_bound ∧ D.asymptotic_bit_lower_bound := by
  letI : Fintype D.foldAlphabet := D.foldFintype
  letI : DecidableEq D.foldAlphabet := D.foldDecidableEq
  have hcapacity :
      D.pom_microcanonical_fold_description_length_lower_bound_classCount ≤ 2 ^ D.bitLength := by
    have hcard := Fintype.card_le_of_injective D.code D.code_injective
    simpa [pom_microcanonical_fold_description_length_lower_bound_classCount] using hcard
  have hbit :
      Nat.clog 2 D.pom_microcanonical_fold_description_length_lower_bound_classCount ≤
        D.bitLength :=
    Nat.clog_le_of_le_pow hcapacity
  refine ⟨hbit, ?_⟩
  have hbit_real :
      (Nat.clog 2 D.pom_microcanonical_fold_description_length_lower_bound_classCount : ℝ) ≤
        (D.bitLength : ℝ) := by
    exact_mod_cast hbit
  have hentropy :
      D.pom_microcanonical_fold_description_length_lower_bound_entropyBits ≤
        (Nat.clog 2 D.pom_microcanonical_fold_description_length_lower_bound_classCount : ℝ) := by
    simpa [pom_microcanonical_fold_description_length_lower_bound_entropyBits,
      pom_microcanonical_fold_description_length_lower_bound_classCount] using D.entropy_log_lower
  exact le_trans hentropy hbit_real

end Omega.POM
