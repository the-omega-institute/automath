import Mathlib.Tactic
import Omega.SPG.PolytimeCompleteInvariantImpliesPEqualsNP

namespace Omega.Folding

/-- The accepting multiplicity `N(x)` of the current audited Block--FoldSAT instance. -/
noncomputable def block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (φ : SatInstance) : ℕ :=
  Fintype.card { a : SatAssignment φ // satEval φ a = true }

/-- The low-temperature two-level partition function
`Z_x(β) = N(x) + 2^{-β} (d_m(x) - N(x))`. -/
noncomputable def
    block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (beta : SatInstance → ℕ) (φ : SatInstance) : ℚ :=
  let acceptCount :=
    block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
      SatAssignment satEval φ
  (acceptCount : ℚ) +
    ((Fintype.card (SatAssignment φ) - acceptCount : ℕ) : ℚ) / (2 ^ beta φ : ℚ)

/-- Threshold classifier extracted from an additive approximation to the low-temperature partition
function. -/
def block_foldsat_low_temperature_partition_function_additive_hardness_decide
    {SatInstance : Type} (approx : SatInstance → ℚ) (φ : SatInstance) : Bool :=
  decide ((1 / 2 : ℚ) ≤ approx φ)

private lemma
    block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count_eq_zero_iff
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (φ : SatInstance) :
    block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
        SatAssignment satEval φ = 0 ↔
      ¬ ∃ a : SatAssignment φ, satEval φ a = true := by
  constructor
  · intro hCount hSat
    rcases hSat with ⟨a, ha⟩
    have hpos :
        0 <
          block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
            SatAssignment satEval φ := by
      unfold block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
      exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
    omega
  · intro hUnsat
    classical
    unfold block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
    letI : IsEmpty { a : SatAssignment φ // satEval φ a = true } :=
      ⟨fun a => hUnsat ⟨a.1, a.2⟩⟩
    simp

private lemma
    block_foldsat_low_temperature_partition_function_additive_hardness_partition_le_one_quarter
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (beta : SatInstance → ℕ)
    (hbeta : ∀ φ, 4 * Fintype.card (SatAssignment φ) ≤ 2 ^ beta φ) (φ : SatInstance)
    (hUnsat : ¬ ∃ a : SatAssignment φ, satEval φ a = true) :
    block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
        SatAssignment satEval beta φ ≤
      1 / 4 := by
  have hCount :
      block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
          SatAssignment satEval φ = 0 := by
    exact
      (block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count_eq_zero_iff
        SatAssignment satEval φ).2 hUnsat
  have hdenPos : (0 : ℚ) < (2 ^ beta φ : ℚ) := by positivity
  have hbound :
      (4 * Fintype.card (SatAssignment φ) : ℚ) ≤ (2 ^ beta φ : ℚ) := by
    exact_mod_cast hbeta φ
  have hdiv :
      ((Fintype.card (SatAssignment φ) : ℚ) / (2 ^ beta φ : ℚ)) ≤ 1 / 4 := by
    have hdenNonzero : (2 ^ beta φ : ℚ) ≠ 0 := by positivity
    field_simp [hdenNonzero]
    nlinarith
  unfold block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
  simp [hCount]
  simpa using hdiv

private lemma
    block_foldsat_low_temperature_partition_function_additive_hardness_partition_ge_one
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (beta : SatInstance → ℕ) (φ : SatInstance)
    (hSat : ∃ a : SatAssignment φ, satEval φ a = true) :
    1 ≤
      block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
        SatAssignment satEval beta φ := by
  rcases hSat with ⟨a, ha⟩
  have hcount :
      1 ≤
        block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
          SatAssignment satEval φ := by
    unfold block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
    exact Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩)
  have htailNonneg :
      0 ≤
        (((Fintype.card (SatAssignment φ) -
            block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
              SatAssignment satEval φ : ℕ) : ℚ) /
          (2 ^ beta φ : ℚ)) := by
    positivity
  have hcountQ :
      (1 : ℚ) ≤
        block_foldsat_low_temperature_partition_function_additive_hardness_accepting_count
          SatAssignment satEval φ := by
    exact_mod_cast hcount
  unfold block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
  nlinarith

private lemma
    block_foldsat_low_temperature_partition_function_additive_hardness_decide_spec
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (beta : SatInstance → ℕ)
    (hbeta : ∀ φ, 4 * Fintype.card (SatAssignment φ) ≤ 2 ^ beta φ)
    (approx : SatInstance → ℚ)
    (hApprox :
      ∀ φ,
        |approx φ -
            block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
              SatAssignment satEval beta φ| ≤
          1 / 8) :
    ∀ φ,
      block_foldsat_low_temperature_partition_function_additive_hardness_decide approx φ = true ↔
        ∃ a : SatAssignment φ, satEval φ a = true := by
  intro φ
  constructor
  · intro hDecide
    have hApproxBounds := abs_le.mp (hApprox φ)
    have hApproxHalf : (1 / 2 : ℚ) ≤ approx φ := by
      simpa [block_foldsat_low_temperature_partition_function_additive_hardness_decide] using hDecide
    by_contra hUnsat
    have hPart :
        block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
            SatAssignment satEval beta φ ≤
          1 / 4 :=
      block_foldsat_low_temperature_partition_function_additive_hardness_partition_le_one_quarter
        SatAssignment satEval beta hbeta φ hUnsat
    linarith
  · intro hSat
    have hApproxBounds := abs_le.mp (hApprox φ)
    have hPart :
        1 ≤
          block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
              SatAssignment satEval beta φ :=
      block_foldsat_low_temperature_partition_function_additive_hardness_partition_ge_one
        SatAssignment satEval beta φ hSat
    have hHalf : (1 / 2 : ℚ) ≤ approx φ := by
      linarith
    simpa [block_foldsat_low_temperature_partition_function_additive_hardness_decide] using hHalf

/-- Paper label: `thm:block-foldsat-low-temperature-partition-function-additive-hardness`. If the
two-level low-temperature partition function admits a uniform additive `1/8` approximation at a
temperature with `2^β ≥ 4 d_m`, then the resulting `1/2` threshold decides the underlying
Block--FoldSAT predicate, and complementing that classifier yields the chapter-local `P = NP`
conclusion. -/
theorem paper_block_foldsat_low_temperature_partition_function_additive_hardness
    {SatInstance : Type} (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (satEval : ∀ φ, SatAssignment φ → Bool) (beta : SatInstance → ℕ)
    (approx : SatInstance → ℚ)
    (hbeta : ∀ φ, 4 * Fintype.card (SatAssignment φ) ≤ 2 ^ beta φ)
    (hApprox :
      ∀ φ,
        |approx φ -
            block_foldsat_low_temperature_partition_function_additive_hardness_partition_function
              SatAssignment satEval beta φ| ≤
          1 / 8) :
    Omega.SPG.PolytimeDecidable (fun φ => ∃ a : SatAssignment φ, satEval φ a = true) ∧
      Omega.SPG.PEqualsNP (fun φ => ∃ a : SatAssignment φ, satEval φ a = true) := by
  have hSpec :
      ∀ φ,
        block_foldsat_low_temperature_partition_function_additive_hardness_decide approx φ =
            true ↔
          ∃ a : SatAssignment φ, satEval φ a = true :=
    block_foldsat_low_temperature_partition_function_additive_hardness_decide_spec
      SatAssignment satEval beta hbeta approx hApprox
  have hSat :
      Omega.SPG.PolytimeDecidable (fun φ => ∃ a : SatAssignment φ, satEval φ a = true) := by
    refine ⟨
      block_foldsat_low_temperature_partition_function_additive_hardness_decide approx,
      trivial,
      hSpec⟩
  exact ⟨hSat, ⟨Omega.SPG.complement_polytime_decidable hSat, hSat⟩⟩

end Omega.Folding
