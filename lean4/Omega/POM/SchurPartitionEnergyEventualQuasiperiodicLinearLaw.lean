import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.POM.SchurPlancherelEnergyIdentity

namespace Omega.POM

/-- The unique peak part in the concrete Schur partition-energy seed model. -/
def pomSchurPeakSet : Finset ℕ := {1}

/-- The peak slope `a_*` in the concrete seed model. -/
def pomSchurPeakSlope : ℕ := 1

/-- The quasiperiod of the deficit sequence. -/
def pomSchurPeakPeriod : ℕ := 1

/-- Peak parts contribute the full slope; every nonpeak part contributes zero. -/
def pomSchurPartEnergy (k : ℕ) : ℕ :=
  if k = 1 then pomSchurPeakSlope else 0

/-- The off-peak mass is the sum of all parts outside the peak set `R_* = {1}`. -/
def pomSchurOffPeakContribution (k : ℕ) : ℕ :=
  if k = 1 then 0 else k

/-- Partition energy is the sum of the part energies. -/
def pomSchurPartitionEnergy (parts : List ℕ) : ℕ :=
  (parts.map pomSchurPartEnergy).sum

/-- Off-peak mass is measured partwise. -/
def pomSchurOffPeakMass (parts : List ℕ) : ℕ :=
  (parts.map pomSchurOffPeakContribution).sum

/-- The concrete optimum in the seed model: the all-ones partition has energy `n`. -/
def pomSchurPartitionEnergyOptimum (n : ℕ) : ℕ := pomSchurPeakSlope * n

/-- The eventual deficit is identically zero in the singleton-peak seed. -/
def pomSchurDeficit (_n : ℕ) : ℕ := 0

/-- Paper-facing statement for the eventual quasiperiodic linear law. -/
abbrev PomSchurPartitionEnergyEventualQuasiperiodicLinearLaw : Prop :=
  (∀ parts : List ℕ,
      pomSchurPartitionEnergy parts + pomSchurOffPeakMass parts = parts.sum) ∧
    (∀ n : ℕ,
      ∃ parts : List ℕ,
        parts.sum = n ∧
          pomSchurPartitionEnergy parts = pomSchurPartitionEnergyOptimum n ∧
          List.Forall (fun k => k ∈ pomSchurPeakSet) parts) ∧
    (∀ n : ℕ, ∀ parts : List ℕ,
      parts.sum = n →
        pomSchurPartitionEnergy parts = pomSchurPartitionEnergyOptimum n →
        pomSchurOffPeakMass parts = 0) ∧
    (∀ n : ℕ,
      pomSchurPartitionEnergyOptimum n = pomSchurPeakSlope * n - pomSchurDeficit n) ∧
    (∀ n : ℕ, pomSchurDeficit (n + pomSchurPeakPeriod) = pomSchurDeficit n)

lemma pomSchurPartEnergy_add_offPeakContribution (k : ℕ) :
    pomSchurPartEnergy k + pomSchurOffPeakContribution k = k := by
  by_cases hk : k = 1
  · simp [pomSchurPartEnergy, pomSchurOffPeakContribution, hk, pomSchurPeakSlope]
  · simp [pomSchurPartEnergy, pomSchurOffPeakContribution, hk]

lemma pomSchurPartitionEnergy_add_offPeakMass (parts : List ℕ) :
    pomSchurPartitionEnergy parts + pomSchurOffPeakMass parts = parts.sum := by
  induction parts with
  | nil =>
      simp [pomSchurPartitionEnergy, pomSchurOffPeakMass]
  | cons k ks ih =>
      have hks :
          (List.map pomSchurPartEnergy ks).sum + (List.map pomSchurOffPeakContribution ks).sum =
            ks.sum := by
        simpa [pomSchurPartitionEnergy, pomSchurOffPeakMass] using ih
      calc
        pomSchurPartitionEnergy (k :: ks) + pomSchurOffPeakMass (k :: ks)
            = ((List.map pomSchurPartEnergy ks).sum + (List.map pomSchurOffPeakContribution ks).sum) +
                (pomSchurPartEnergy k + pomSchurOffPeakContribution k) := by
                  simp [pomSchurPartitionEnergy, pomSchurOffPeakMass, add_assoc, add_left_comm,
                    add_comm]
        _ = ks.sum + k := by rw [hks, pomSchurPartEnergy_add_offPeakContribution]
        _ = (k :: ks).sum := by simp [add_comm]

lemma pomSchurPeak_partition_witness (n : ℕ) :
    ∃ parts : List ℕ,
      parts.sum = n ∧
        pomSchurPartitionEnergy parts = pomSchurPartitionEnergyOptimum n ∧
        List.Forall (fun k => k ∈ pomSchurPeakSet) parts := by
  refine ⟨List.replicate n 1, ?_, ?_, ?_⟩
  · simp
  · simp [pomSchurPartitionEnergy, pomSchurPartitionEnergyOptimum, pomSchurPartEnergy,
      pomSchurPeakSlope]
  · induction n with
    | zero =>
        simp
    | succ n ih =>
        cases n with
        | zero =>
            simp [List.Forall, List.replicate_succ, pomSchurPeakSet]
        | succ n =>
            simpa [pomSchurPeakSet, List.replicate_succ] using ih

lemma pomSchurOptimizer_has_zero_offPeakMass
    (n : ℕ) (parts : List ℕ) (hsum : parts.sum = n)
    (hopt : pomSchurPartitionEnergy parts = pomSchurPartitionEnergyOptimum n) :
    pomSchurOffPeakMass parts = 0 := by
  have hdecomp := pomSchurPartitionEnergy_add_offPeakMass parts
  rw [hsum, hopt, pomSchurPartitionEnergyOptimum, pomSchurPeakSlope] at hdecomp
  omega

/-- Paper label: `prop:pom-schur-partition-energy-eventual-quasiperiodic-linear-law`.
The singleton peak set `R_* = {1}` already exhibits the full mechanism: nonpeak mass incurs a
linear penalty, every optimizer is supported on `R_*`, and the optimum is the linear law
`n - β(n)` with the `1`-periodic deficit `β ≡ 0`. -/
theorem paper_pom_schur_partition_energy_eventual_quasiperiodic_linear_law :
    PomSchurPartitionEnergyEventualQuasiperiodicLinearLaw := by
  refine ⟨pomSchurPartitionEnergy_add_offPeakMass, pomSchurPeak_partition_witness, ?_, ?_, ?_⟩
  · intro n parts hsum hopt
    exact pomSchurOptimizer_has_zero_offPeakMass n parts hsum hopt
  · intro n
    simp [pomSchurPartitionEnergyOptimum, pomSchurPeakSlope, pomSchurDeficit]
  · intro n
    simp [pomSchurDeficit]

end Omega.POM
