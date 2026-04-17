import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The two partition types of `2`, used as a concrete seed for the Schur-Plancherel identity. -/
inductive SchurPartitionIndex
  | cycle
  | split
  deriving DecidableEq, Fintype

open SchurPartitionIndex

lemma sum_over_schur_partition_index {R : Type*} [AddCommMonoid R]
    (f : SchurPartitionIndex → R) : (∑ x, f x) = f cycle + f split := by
  have huniv : (Finset.univ : Finset SchurPartitionIndex) = {cycle, split} := by
    ext x
    cases x <;> simp
  rw [huniv]
  simp

/-- The centralizer weight `z_nu` for each conjugacy class of `S_2`. -/
def schurWeight : SchurPartitionIndex → ℝ
  | cycle => 2
  | split => 2

/-- The irreducible dimensions `f^lambda` in the `S_2` seed model. -/
def schurDegree : SchurPartitionIndex → ℝ
  | cycle => 1
  | split => 1

/-- The `S_2` character table, written in partition coordinates. -/
def schurCharacter : SchurPartitionIndex → SchurPartitionIndex → ℝ
  | cycle, cycle => 1
  | cycle, split => 1
  | split, cycle => 1
  | split, split => -1

/-- The cycle-type monomials whose squared `L^2` mass is measured. -/
def schurCycleMonomial (m : ℝ) : SchurPartitionIndex → ℝ
  | cycle => m + 1
  | split => m - 1

/-- The normalized Schur-channel trace obtained from the partition expansion. -/
def schurNormalizedChannelTrace (m : ℝ) (lam : SchurPartitionIndex) : ℝ :=
  ∑ nu, (schurCharacter lam nu / schurWeight nu) * schurCycleMonomial m nu

/-- Class-function energy in partition coordinates. -/
def schurClassEnergy (m : ℝ) : ℝ :=
  ∑ nu, (1 / schurWeight nu) * (schurCycleMonomial m nu) ^ (2 : ℕ)

/-- Sum of squares of normalized Schur-channel traces. -/
def schurChannelSquareSum (m : ℝ) : ℝ :=
  ∑ lam, (schurNormalizedChannelTrace m lam / schurDegree lam) ^ (2 : ℕ)

/-- Column orthogonality in the `S_2` seed model. -/
lemma schurColumnOrthogonality (nu mu : SchurPartitionIndex) :
    (∑ lam, schurCharacter lam nu * schurCharacter lam mu) =
      if nu = mu then schurWeight nu else 0 := by
  cases nu <;> cases mu
  · rw [sum_over_schur_partition_index]
    norm_num [schurCharacter, schurWeight]
  · rw [sum_over_schur_partition_index]
    norm_num [schurCharacter, schurWeight]
    decide
  · rw [sum_over_schur_partition_index]
    norm_num [schurCharacter, schurWeight]
    decide
  · rw [sum_over_schur_partition_index]
    norm_num [schurCharacter, schurWeight]

lemma schurClassEnergy_closed_form (m : ℝ) : schurClassEnergy m = m ^ (2 : ℕ) + 1 := by
  rw [schurClassEnergy, sum_over_schur_partition_index]
  simp [schurCycleMonomial, schurWeight]
  ring_nf

lemma schurNormalizedChannelTrace_cycle (m : ℝ) :
    schurNormalizedChannelTrace m cycle = m := by
  rw [schurNormalizedChannelTrace, sum_over_schur_partition_index]
  simp [schurCharacter, schurWeight, schurCycleMonomial]
  ring_nf

lemma schurNormalizedChannelTrace_split (m : ℝ) :
    schurNormalizedChannelTrace m split = 1 := by
  rw [schurNormalizedChannelTrace, sum_over_schur_partition_index]
  simp [schurCharacter, schurWeight, schurCycleMonomial]
  ring_nf

lemma schurChannelSquareSum_closed_form (m : ℝ) : schurChannelSquareSum m = m ^ (2 : ℕ) + 1 := by
  rw [schurChannelSquareSum, sum_over_schur_partition_index,
    schurNormalizedChannelTrace_cycle, schurNormalizedChannelTrace_split]
  simp [schurDegree]

/-- The partition-side class-energy formula. -/
def schurPlancherelClassEnergyFormula : Prop :=
  ∀ m : ℝ, schurClassEnergy m = ((schurCycleMonomial m cycle) ^ (2 : ℕ) +
    (schurCycleMonomial m split) ^ (2 : ℕ)) / 2

/-- The Schur-side square-sum formula. -/
def schurPlancherelChannelSquareSumFormula : Prop :=
  ∀ m : ℝ, schurClassEnergy m = schurChannelSquareSum m

/-- Paper-facing `S_2` seed for the Schur-Plancherel energy identity.
    thm:pom-schur-plancherel-energy-identity -/
theorem paper_pom_schur_plancherel_energy_identity :
    schurPlancherelClassEnergyFormula ∧ schurPlancherelChannelSquareSumFormula := by
  refine ⟨?_, ?_⟩
  · intro m
    rw [schurClassEnergy_closed_form]
    simp [schurCycleMonomial]
    ring_nf
  · intro m
    have hclass := schurClassEnergy_closed_form m
    have hchannels := schurChannelSquareSum_closed_form m
    linarith

end
end Omega.POM
