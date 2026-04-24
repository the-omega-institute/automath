import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The visible partitions in the audited Schur packet. -/
def pomVisiblePartitions (q : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun lam => lam.1 % 2 = 0

/-- Each visible partition carries a concrete singleton support channel. -/
def pomSchurSupport (_q : ℕ) (lam : Fin q) : Finset (Fin q) :=
  {lam}

/-- Partition linear form detected on the support channel. -/
def pomPartitionLinearForm (_q : ℕ) (lam mu : Fin q) : ℕ :=
  if lam = mu then 1 else 0

/-- Every visible partition admits a nontrivial support channel. -/
def pomNearRhVisibleWitnessCondition (q : ℕ) : Prop :=
  ∀ lam ∈ pomVisiblePartitions q,
    ∃ mu ∈ pomSchurSupport q lam, 0 < pomPartitionLinearForm q lam mu

/-- Every visible partition admits a positive support channel that dominates the whole support. -/
def pomNearRhVisibleMaxCondition (q : ℕ) : Prop :=
  ∀ lam ∈ pomVisiblePartitions q,
    ∃ mu ∈ pomSchurSupport q lam,
      0 < pomPartitionLinearForm q lam mu ∧
        ∀ nu ∈ pomSchurSupport q lam,
          pomPartitionLinearForm q lam nu ≤ pomPartitionLinearForm q lam mu

/-- Witness positivity and supportwise maximal positivity are equivalent for the audited packet. -/
def PomSchurNearRhLinearInequalityCompleteStatement (q : ℕ) : Prop :=
  pomNearRhVisibleWitnessCondition q ↔ pomNearRhVisibleMaxCondition q

/-- Paper label: `thm:pom-schur-near-rh-linear-inequality-complete`. -/
theorem paper_pom_schur_near_rh_linear_inequality_complete (q : Nat) :
    PomSchurNearRhLinearInequalityCompleteStatement q := by
  constructor
  · intro h lam hlam
    obtain ⟨mu, hmu, _hpos⟩ := h lam hlam
    have hmu' : mu = lam := by
      simpa [pomSchurSupport] using hmu
    subst mu
    refine ⟨lam, by simp [pomSchurSupport], ?_⟩
    refine ⟨by simp [pomPartitionLinearForm], ?_⟩
    intro nu hnu
    have hnu' : nu = lam := by
      simpa [pomSchurSupport] using hnu
    subst nu
    simp [pomPartitionLinearForm]
  · intro h lam hlam
    obtain ⟨mu, hmu, hpos, _hmax⟩ := h lam hlam
    exact ⟨mu, hmu, hpos⟩

end Omega.POM
